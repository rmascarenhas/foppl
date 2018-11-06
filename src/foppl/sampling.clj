(ns foppl.sampling
  "Implements the sampling algorithms for the calculation of the
  posterior of the distribution represented by a graphical
  model. Currently implemented algorithms are Metropolis-within-Gibbs
  and Hamiltonian Monte Carlo."
  (:require [clojure.set :as set]
            [clojure.edn :as edn]
            [anglican.runtime :as anglican]
            [foppl.ast :as ast :refer [accept]]
            [foppl.eval :as eval]
            [foppl.formatter :as formatter]
            [foppl.operations :as operations]
            [foppl.toposort :as toposort]
            [foppl.autodiff :as autodiff]
            [foppl.utils :as utils])
  (:import [foppl.ast constant variable if-cond fn-application definition literal-vector
            literal-map definition local-binding]))

(def ^:private uniform01
  (anglican/uniform-continuous 0 1))

;;;;;;;;;;;;;;;;;;;;
;; GIBBS SAMPLING ;;
;;;;;;;;;;;;;;;;;;;;

;; lists all of the known/expected distribution function supported by FOPPL.
;; This list of distributionns was extracted from those supported by Anglican,
;; on which this implementation depends.
(def ^:private distributions
  #{'bernoulli
    'beta
    'binomial
    'categorical
    'dirichlet
    'discrete
    'exponential
    'flip
    'gamma
    'normal
    'poisson
    'uniform-continuous
    'uniform-discrete
    'wishart
    })

;; modifies an expression in FOPPL's deterministic language replacing
;; calls to distribution functions (e.g., `normal`) to fully qualified
;; function names (`anglican.runtime/normal`). This is so that
;; expressions generated in the graphical model's link functions can
;; be evaluated in arbitrary environments without having to refer to
;; `anglican.runtime` functions.
(defrecord anglican-qualify-visitor [])

(extend-type anglican-qualify-visitor
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during Anglican qualification"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during Anglican qualification"))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during Anglican qualification"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during Anglican qualification"))

  (visit-constant [_ c]
    c)

  (visit-variable [_ variable]
    variable)

  (visit-definition [_ _]
    (utils/ice "No definitions allowed in determistic language (during Anglican qualification)"))

  (visit-local-binding [_ _]
    (utils/ice "No local bindings allowed in deterministic language (during Anglican qualification)"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [qualified-predicate (accept predicate v)
          qualified-then (accept then v)
          qualified-else (accept else v)]
      (ast/if-cond. qualified-predicate qualified-then qualified-else)))

  (visit-fn-application [v {name :name args :args}]
    (let [fn-name (if (contains? distributions name) (symbol (str "anglican.runtime/" name)) name)
          qualified-args (map (fn [n] (accept n v)) args)]
      (ast/fn-application. fn-name qualified-args)))

  (visit-sample [_ _]
    (utils/ice "No `sample` allowed in deterministic language (during Anglican qualification)"))

  (visit-observe [_ _]
    (utils/ice "No `observe` allowed in deterministic language (during Anglican qualification)"))
  )

;; Extracts all constants from an expression, substituting them for
;; access to a map (of name `constants` given). For example, the
;; expression:
;;
;;      (inc 1)
;;
;; is transformed by this visitor to:
;;
;;     [(inc (get constants-1234 (symbol "constant-4321"))), {constant-4321 1}]
;;
;; This is useful to avoid recalculating some constant values such as
;; distributions.  See usage of this visitor in the `perform`
;; function.
(defrecord constant-extract-visitor [registry constants])

(extend-type constant-extract-visitor
  ast/visitor

  (visit-constant [{registry :registry constants :constants} {c :n}]
    (let [;; generate a new name for the constant
          name (ast/fresh-sym "c")
          s-name (ast/fn-application. 'symbol [(ast/constant. (str name))])

          ;; replace the constant with a function to `get` on the map
          ;; of constants
          get-constant (ast/fn-application. 'get [constants s-name])]

      ;; add the value of the constant to the registry
      [get-constant (assoc registry name c)]))

  (visit-variable [{registry :registry} var]
    [var registry])

  (visit-literal-vector [{registry :registry} literal-vector]
    [literal-vector registry])

  (visit-literal-map [{registry :registry} literal-map]
    [literal-map registry])

  (visit-definition [{registry :registry} definition]
    [definition registry])

  (visit-local-binding [{registry :registry} local-binding]
    [local-binding registry])

  (visit-foreach [{registry :registry} foreach]
    [foreach registry])

  (visit-loop [{registry :registry} loop]
    [loop registry])

  (visit-if-cond [{registry :registry :as v} {predicate :predicate then :then else :else}]
    (let [[predicate-e predicate-r] (accept predicate v)
          [then-e then-r] (accept then v)
          [else-e else-r] (accept else v)]
      [(ast/if-cond. predicate-e then-e else-e) (merge registry predicate-r then-r else-r)]))

  (visit-fn-application [{registry :registry :as v} {name :name args :args}]
    (let [pairs (map (fn [n] (accept n v)) args)
          args-e (map first pairs)
          registries (map second pairs)]
      [(ast/fn-application. name args-e) (apply merge (cons registry registries))]))

  (visit-sample [{registry :registry} sample]
    [sample registry])

  (visit-observe [{registry :registry} observe]
    [observe registry])
  )

(defn- extract-constants [n map-name]
  "Given an AST node `n` and a fresh name `map-name`, this will
  substitute constant values in the AST by fresh names, and return a
  map from names to constant values."
  (let [visitor (constant-extract-visitor. {} (ast/variable. map-name))]
    (accept n visitor)))

(defn- latent-vars [{V :V Y :Y}]
  "Given the graph component of a graphical model, this function
  returns the set of latent functions of the graph (i.e., the set of
  vertices that were not observed."
  (set/difference V (set (keys Y))))

(defn- sample [dist]
  "Samples from a standard distribution. Relies on Anglican's
  implementation of sampling. The `dist` parameter should be an
  Anglican distributiob object."
  (anglican/sample* dist))

(defn- log-prob [dist v]
  "Calculates the log-probability of `dist` and value `v`. Relies on
  Anglican's implementation."
  (anglican/observe* dist v))

(defn- eval-proposal [proposal xs]
  "Evaluates a proposal distribution under a given set of assignments
  `xs`. The proposal is expected to be given as an anonymous function
  that can be directly invoked."
  (proposal xs))

(defn- choose-proposal [{V :V P :P Y :Y} compiled-P proposals x xs xs']
  "This function decides whether to accept a new assignment of random
  variables `xs'` or to maintain the current assignment `xs`. The
  first argument is the graph component of a graphical model, and
  `proposals` is a map of proposal distributions mapping from
  random-variable name to its proposed distribution (given as an AST
  node). Returns either `xs` or `xs'`. For more extensive information
  on how the algorithm works, check section 3.3 of the Introduction to
  Probabilistic Programming book."
  (let [ ;; evaluate resulting proposal distributions based on existing
        ;; and proposed set of assignments.
        d (eval-proposal (get proposals x) xs)
        d' (eval-proposal (get proposals x) xs')

        ;; Validation step: `d` and `d'` should both be distribution
        ;; objects
        _ (when-not d' (utils/ice "Cannot build new proposed distribution"))

        ;; log-a is the log probability of the alpha component, which
        ;; is used to decide whether to accept or reject the proposed
        ;; set of assignments
        c (get xs x)
        c' (get xs' x)

        log-a (- (log-prob d' c) (log-prob d c'))

        ;; calculate a map from {random-variable name -> set of free
        ;; variables in its link function}.
        node-free-vars (fn [name] (ast/free-vars (get P name)))
        free-vars (zipmap V (map node-free-vars V))

        ;; Vx is the Markov Blanket of random variable `x`. In terms
        ;; of a graphical model representation, this set consists of
        ;; all vertices `v` in the graph where `x` is free in the link
        ;; function of `v`.
        dependence (fn [s v] (if (contains? (get free-vars v) x) (set/union s #{v}) s))
        Vx (reduce dependence #{} V)

        ;; given an expression `e`, this performs a sequence of
        ;; substitutions based on the `subs` map from names to
        ;; constants. Returns the resulting expression
        ;; substitute-coll (fn [e subs] (reduce
        ;;                              (fn [e [name const]] (ast/substitute name (ast/constant. const) e))
        ;;                              e
        ;;                              subs))

        ;; maps observed random variables names to the raw
        ;; constant value that was observed
        observations (zipmap (keys Y) (map :n (vals Y)))

        ;; this function is responsible for calculating the log-a
        ;; component according to the formula that defines the
        ;; Metropolis-within-Gibbs algorithm.
        evaluate-proposals (fn [log-a v] (let [ ;; the PDF function associated with vertex `v`
                                              pdf (get compiled-P v)

                                              ;; calculate current and proposed map of random
                                              ;; variable assignments
                                              current-vals (merge observations xs)
                                              proposed-vals (merge observations xs')

                                              ;; evaluate PDF according to current and proposed
                                              ;; random variable assignments
                                              current-pdf (pdf current-vals)
                                              proposed-pdf (pdf proposed-vals)]

                                          ;; return the corresponding updated log-a value
                                          (- (+ log-a proposed-pdf) current-pdf)))

        ;; perform the update of log-a for each vertex in `Vx`
        log-a (reduce evaluate-proposals log-a Vx)

        ;; obtain the value of the alpha component from `log-a`
        a (Math/exp log-a)

        ;; sample from a Uniform(0, 1) distribution
        u (anglican/sample* uniform01)]

    ;; decide between current and proposed states
    (if (< u a) xs' xs)))

(defn- handle-var [graph proposals decide xs x]
  "Updates random variable assignment for a single random variable `x`
  in the set of latent variables `xs` and decides whether the update
  should be accepted or rejected (see actual decision procedure in
  `choose-proposal`. The `decide` argument should be a decision
  function that, when applied with arguments 1) random variable `x`;
  2) current assignment `xs`; and 3) proposed assignment `xs'`, should
  return either one of `xs` or `xs'`. Returns either `xs` or an
  updated assignment of random variables."
  (let [proposed-dist (eval-proposal (get proposals x) xs)

        ;; validation step: make sure the proposal distribution
        ;; evaluated to a valid distribution object
        _ (when-not proposed-dist (utils/ice "Cannot build proposed distribution"))

        ;; propose new assignment of random variables by updating
        ;; entry on variable `x`
        xs' (assoc xs x (sample proposed-dist))]
    (decide x xs xs')))

(defn- gibbs-step [{graph :G :as model} compiled-P xs proposals]
  "Performs one step of a Gibbs sampling algorithm. The algorithm
  updates the assignments for one latent variable at a time and
  decides whether the proposed assignment should be accepted or
  rejected. The `xs` argument should be the initial assignment of
  random-variables. The `proposals` argument is a map from random
  variable names to proposal distributions, represented as AST
  nodes (possibly with free variables)."
  (let [;; calculate the set of latent variables in the graph given
        latent (latent-vars graph)

        ;; variables should be handled in topological order.
        ordering (toposort/perform model)

        ;; random-variables to be considered should be those that were
        ;; not observed in the model, in the topological order
        ;; calculated above
        unobserved? (partial contains? latent)
        random-vars (filter unobserved? ordering)

        ;; the decision function is `choose-proposal`, partially
        ;; applied with the graph and proposals map already known at
        ;; this point.
        decide (partial choose-proposal graph compiled-P proposals)

        ;; function invoved for each of the random variables that
        ;; compute a proposed set of random-variable assignments and
        ;; decide whether to accept or reject it.
        propose-accept (partial handle-var graph proposals decide)]

    ;; iterate over random variables, with initial assignment
    ;; `xs`. Returns the updated random-variable assignment.
    (reduce propose-accept xs random-vars)))

(defn- init-gibbs [{{P :P} :G :as model} latent initial]
  "Initializes the Metropolis-within-Gibbs sampling algorithm. Uses a
  fixed size burn-in period by performing 5,000 Gibbs steps. Returns
  the initial map of assignments resulting from the burn-in, and a
  function that performs a single step of the Gibbs, to be used when
  generating a lazy sequence of samples."
  (let [;; extracts distribution AST node from a link function (which
        ;; should be in the format (observe* dist val)
        extract-dist (fn [x] (first (:args (get P x))))

        ;; link functions for each of the latent variables in the
        ;; model
        link-fns (map extract-dist latent)

        ;; given an AST node `n`, this helper function will generate a
        ;; Clojure anonymous function that can then be directly
        ;; invoked in order to calculate a value for the expression.
        ;; The generated function accepts a single argument: a map
        ;; containing the values of all free variables in the
        ;; expression.
        make-lambda (fn [n] (let [;; let `m` be the name of the map taken as parameter
                                 ;; in this anonymous function
                                 m 'm

                                 ;; the free variables of the expression are going to be
                                 ;; random variables referenced in it
                                 random-vars (ast/free-vars n)

                                 ;; generate a fresh name for the map of constants
                                 constants-map-name (ast/fresh-sym "constants")

                                 ;; extract the updated expression and map of constants in the
                                 ;; expression. This is an unfortunate consequence of the fact that
                                 ;; we don't want constant values like "(normal 1 1)" to be interpreted
                                 ;; as function calls and recomputed on every application of the
                                 ;; generated function.
                                 [link constants] (extract-constants n constants-map-name)

                                 ;; fully qualify distribution functions so that the link function
                                 ;; can be compiled to a Clojure anonymous function regardless of
                                 ;; the functions referred in this namespace
                                 anglican-qualify (fn [n] (accept n (anglican-qualify-visitor.)))
                                 link (anglican-qualify link)

                                 ;; parameter to be passed to the anonymous function
                                 assignments (ast/variable. m)

                                 ;; AST variable node representing the map of constants
                                 constants-map (ast/variable. constants-map-name)

                                 ;; substitute free variables in the expression by accesses to the
                                 ;; map of assignments that is to be passed when the generated function
                                 ;; is invoked
                                 map-name (fn [name] (ast/fn-application. 'symbol [(ast/constant. (str name))]))
                                 get-var (fn [name] (ast/fn-application. 'get [assignments (map-name name)]))
                                 substitute-random-v (fn [e name] (ast/substitute name (get-var name) e))
                                 substituted-link-fn (reduce substitute-random-v link random-vars)

                                 ;; generate an AST node representing the anonymous function we want
                                 lambda (ast/definition. nil [constants-map assignments] substituted-link-fn)
                                 serialize (fn [n] (formatter/to-str n))

                                 ;; to transfor this into a Clojure lambda, we serialize our AST
                                 ;; representation and have Clojure evaluate the expression
                                 to-clj (fn [n] (eval (edn/read-string (serialize n))))]

                             ;; partially apply the lambda with the map of constants so that users
                             ;; of the function need only pass the map of assignments, which vary
                             ;; on different iterations of the sampling algorithm
                             (partial (to-clj lambda) constants)))

        ;; generate a map from random-variable => Clojure anonymous function
        compiled-P (reduce (fn [m [name n]] (assoc m name (make-lambda n))) {} P)

        ;; set of proposed distributions are the link functions in the
        ;; graphical model
        proposals (zipmap latent (map make-lambda link-fns))

        ;; run the Metropolis-within-Gibbs algorithm for `n`
        ;; iterations, given the initial assignment of random
        ;; variables `xs`. Returns a map with keys `:xs` and `:data`,
        ;; where `xs` is the assignment map for the last iteration,
        ;; and `data` is a vector containing the assignments for every
        ;; iteration of the algorithm.
        gibbs (fn [n xs]
                (reduce
                 (fn [{xs :xs data :data} _]
                   (let [xs (gibbs-step model compiled-P xs proposals)]
                     {:xs xs :data (conj data xs)}))
                 {:xs xs :data []}
                 (repeat n nil)))

        ;; burn-in state: run the algorithm a number of times to make
        ;; sure we get a set of variable assignments that are "within"
        ;; the posterior distribution
        {burned-in :xs} (gibbs 5000 initial)

        ;; the `gibbs` helper function defined above is a lot more
        ;; general and is able to run `n` gibbs steps. However, in
        ;; order to generate our lazy sequence, we write a wrapper for
        ;; it that, given a map of assignments, produces a new map of
        ;; assignments as a result of running a single gibbs step
        next-sample (fn [xs] (:xs (gibbs 1 xs)))]

    ;; return the map of assignments that should be used to initiate
    ;; the algorithm, and the function that, given a map of
    ;; assignments, produces the next one.
    [burned-in next-sample]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HAMILTONIAN MONTE CARLO SAMPLING ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; a gradient represents an anonymous Clojure function that computes
;; the gradient of some other pre-computed function.  In the case of
;; Hamiltonian Monte Carlo, we want to calculate partial derivatives
;; of the potential energy of the model at different
;; iterations. `args` is the sequence of formal parameters that the
;; lambda takes.
(defrecord gradient [lambda args])

;; This is responsible for transforming an expression with `observe*`
;; function applications into applications of `normpdf`, so a to make
;; the function differentiable using the `autodiff` library.
(defrecord observe-normpdf-visitor [])

(extend-type observe-normpdf-visitor
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "Found literal vector while transforming normpdf"))

  (visit-literal-map [_ _]
    (utils/ice "Found literal-map while transforming normpdf"))

  (visit-foreach [_ _]
    (utils/ice "Found foreach while transforming normpdf"))

  (visit-loop [_ _]
    (utils/ice "Found loop while transforming normpdf"))

  (visit-constant [_ {dist :n :as constant}]
    (let [class-dist (str (class dist))
          anglican-dist (re-matches #".*anglican.runtime.(.*)-distribution" class-dist)
          dirac-dist? (re-matches #".*foppl.primitives.dirac-distribution" class-dist)
          distribution-object? (or anglican-dist dirac-dist?)
          dist-id (if dirac-dist? "dirac" (last anglican-dist))]

      ;; we can only compute the derivative of the PDF of normal
      ;; distributions -- throw an error if we visit a different kind
      ;; of distribution.  This visitor will return the distribution
      ;; parameters as a collection. The parameters will be collected
      ;; on the visit to the corresponding `observe*` call as this
      ;; visitor traverses the AST.
      (cond
        (not distribution-object?) constant
        (= dist-id "normal") [(ast/constant. (:mean dist)) (ast/constant. (:sd dist))]
        :else (utils/foppl-error (str "Do not know how to compute derivative of distribution: " dist-id)))))

  (visit-variable [_ variable]
    variable)

  (visit-definition [_ _]
    (utils/ice "Found definition while transforming normpdf"))

  (visit-local-binding [_ _]
    (utils/ice "Found local binding while transforming normpdf"))

  (visit-if-cond [_ if-cond]
    if-cond)

  (visit-fn-application [v {name :name args :args}]
    (cond
      ;; if we are visiting an `observe*` call, transform the node to
      ;; an application of `normpdf`, where the first parameter is the
      ;; observed value, and the remaining are the parameters of the
      ;; distribution -- in this case, the mean and standard
      ;; deviation.
      (= name 'anglican.runtime/observe*) (ast/fn-application. 'normpdf (cons (second args) (accept (first args) v)))

      ;; if this is a visit to a distribution object, return its the
      ;; distribution parameters.  This follows the same signature of
      ;; the `visit-constant` method when the constant is an Anglican
      ;; distribution object.
      (contains? distributions name) (into [] args)

      ;; if the function is not related to distributions or
      ;; observations, recursively transform the function arguments.
      :else (ast/fn-application. name (map (fn [n] (accept n v)) args))))

  (visit-sample [_ _]
    (utils/ice "Found `sample` while transforming normpdf"))

  (visit-observe [_ _]
    (utils/ice "Found `observe` while transforming normpdf")))

(defn- accept-coll [coll v]
  "Visits every node in the collection `coll` using visitor `v`,
  returning the resulting collection."
  (map (fn [n] (accept n v)) coll))

;; This visitor is able to rename functions in arbitrarily complex expressions.
;; After an expression is visited by this visited by this visitor, every function
;; call to `from` becomes a function call to `to`
(defrecord rename-fn-visitor [from to])

(extend-type rename-fn-visitor
  ast/visitor

  (visit-literal-vector [v {es :es}]
    (ast/literal-vector. (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (ast/literal-map. (accept-coll es v)))

  (visit-foreach [_ _]
    (utils/ice "foreach should have been desugared during normpdf qualification"))

  (visit-loop [_ _]
    (utils/ice "loop should have been desugared during normpdf qualification"))

  (visit-constant [_ c]
    c)

  (visit-variable [_ variable]
    variable)

  (visit-definition [v {name :name args :args e :e}]
    (ast/definition. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          qualified-bindings (mapcat (fn [[name val]] [name (accept val v)]) pairs)]
      (ast/local-binding. qualified-bindings (accept-coll es v))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [{from :from to :to :as v} {name :name args :args}]
    (if (= name from)
      (ast/fn-application. to (accept-coll args v))
      (ast/fn-application. name (accept-coll args v))))

  (visit-sample [_ _]
    (utils/ice "No `sample` should exist when qualifying normpdf"))

  (visit-observe [_ _]
    (utils/ice "No `observe` should exist when qualifying normpdf")))

(defn- apply-gradient [{lambda :lambda args :args} xs]
  "Given a gradient and a map of assignments `xs`, this function will
  return the gradient 'vector' as a map that associates random
  variable names with their partial derivatives."
  (let [[_ grad] (apply lambda xs)]
    grad))

(defn- potential-energy-gradient [{{P :P Y :Y} :G} latent]
  "Generates a gradient anonymous function (represented as a
  `gradient` record with accompanying sequence of parameters) that,
  when invoked, produces a list of partial derivatives with respect to
  each random variable in the potential energy of the graphical system
  in a Hamiltonian Monte Carlo sampling algorithm."
  (let [ ;; pairs up additions in an expression, i.e., (+ 1 2 3 4)
        ;; becomes (+ 1 (+ 2 (+ 3 4))). This is so that the automatic
        ;; differention library will be able to produce partial
        ;; derivatives for the potential energy of the system.
        pair-up-addition (fn pair-up [{name :name args :args :as sum}]
                           (let [add (fn [nums] (ast/fn-application. '+ nums))]

                             ;; the AST node given to this function *must* be a function
                             ;; application of `+`.
                             (when-not (= name '+)
                               (utils/foppl-error (str "Not an addition function: " name)))

                             (cond
                               ;; if there is only one argument, introduce an extra
                               ;; `0` so that addition will have two parameters
                               (= (count args) 1) (add [(first args) (ast/constant. 0)])

                               ;; if this is an addition of two expressions, no changes
                               ;; are necessary
                               (= (count args) 2) sum

                               ;; otherwise, we are adding more than two expressions.
                               ;; The resulting expression is the sum of the first expression,
                               ;; and a recursive call to the rest of the expressions.
                               :else (add [(first args) (pair-up (add (rest args)))]))))


        ;; helper higher-order function that, given a two function
        ;; names, will produce a function that, when invoked with an
        ;; AST node `n`, will replace every call of `from` to calls of
        ;; `to` in `n`.
        rename-fn (fn [from to] (fn [n] (accept n (rename-fn-visitor. from to))))

        ;; helper function to transform an expression in order to make
        ;; it differentiable.  Used in the potential energy
        ;; formula. First, changes calls to `observe*` to calls to
        ;; `normpdf`, and then it pairs up additions
        transform-pdf (fn [n] (-> n
                                 (accept (observe-normpdf-visitor.))
                                 pair-up-addition))

        ;; helper function that, given an AST representation of an
        ;; anonymous function definition, compiles it to a Clojure
        ;; lambda.
        to-lambda #(-> %
                       formatter/to-str
                       edn/read-string
                       eval)

        ;; given an AST node `n`, this function will qualify
        ;; applications of `normpdf`, appending the namespace where
        ;; its implementation can be found: `foppl.autodiff/normpdf`.
        ;; This is so that Clojure can successfully compile the
        ;; derivative-calculating function into an anonymous function.
        qualify-normpdf (rename-fn 'normpdf 'foppl.autodiff/normpdf)

        ;; potential energy formula. See section 3.4.1 of the book for a representation
        ;; in mathematical notation
        observed-vars (keys Y)

        Ex-terms (map (fn [x] (get P x)) latent)
        Ey-terms (map (fn [y] (ast/substitute y (get Y y) (get P y))) observed-vars)

        Ex (ast/fn-application. '+ Ex-terms)
        Ey (ast/fn-application. '+ Ey-terms)

        ;; arguments passed to the function that calculates potential
        ;; energy (or its partial derivatives) is the set of latent
        ;; variables of the model.
        energy-formal-args (into [] latent)
        energy-args (map #(ast/variable. %) energy-formal-args)

        ;; formula for the potential energy.
        Eu (ast/fn-application. '* [(ast/constant. -1.0) (ast/fn-application. '+ [Ex Ey])])

        ;; make a lambda that calculates the potential energy of the
        ;; system given a set of assignments to the random
        ;; variables. Before parsing to a Clojure anonymous function,
        ;; qualify every call to Anglican functions so Clojure will be
        ;; able to resolve all symbols.
        Eu-defn (ast/definition. nil energy-args (accept Eu (anglican-qualify-visitor.)))
        Eu-fn (to-lambda Eu-defn)

        ;; potential energy formula, transformed in such a way as to
        ;; be differentiable by the `autodiff` library.
        diff-Eu (ast/fn-application. '* [(ast/constant. -1.0) (ast/fn-application. '+ [(transform-pdf Ex) (transform-pdf Ey)])])

        ;; generate an anonymous function that calculates the
        ;; potential energy of the model.
        diff-Eu-fn (ast/definition. nil energy-args diff-Eu)

        ;; generate a function that computes the gradient of the
        ;; potential energy of the model with respect to the latent
        ;; variables.
        gradient-Eu (autodiff/perform-tree diff-Eu-fn)

        ;; qualify calls to `normpdf` to be independent of evaluation
        ;; namespace.
        qualified-gradient (-> gradient-Eu
                               ast/to-tree
                               qualify-normpdf)

        ;; compile the gradient function to a Clojure anonymous
        ;; function.
        gradient-fn (to-lambda qualified-gradient)]

    ;; returns an instance of the `gradient` record with the anonymous
    ;; function computed above, and the list of formal arguments it
    ;; expects.
    [Eu-fn (gradient. gradient-fn energy-formal-args)]))

(defn- mvn-mass-matrix [n M]
  "Builds a Multivariate Normal distribution (MVN) for a graphical
  model with `n` latent variables, where the mass of each is constant
  `M`. Returns an Anglican representation of the distribution, which
  can then be sampled to get a collection of sampled values."

  (let [;; produce a diagonal matrix where each non-zero element is
        ;; equal to the mass `M` given.
        matrix (reduce #(conj % (assoc (into [] (repeat n 0)) %2 M)) [] (range n))]

    ;; the `mvn` function takes as first argument a collection of
    ;; means (in a mass matrix, they are always zero), and a
    ;; covariance matrix, represented by the diagonal matrix computed
    ;; above.
    (anglican/mvn (repeat n 0) matrix)))

(defn- scalar-vector-op [f scalar vector]
  "Performs an operation, represented by function `f`, between a
  scalar value and a vector. Returns a vector."
  (mapv #(f scalar %) vector))

(defn- vector-op [f va vb]
  {:pre [(= (count va) (count vb))]}
  "Performs an operation, represented by function `f`, over two
  vectors `va` and `vb`, which must be of same length. Returns a
  vector."

  (let [zipped (map vector va vb)]
    (mapv (fn [[a b]] (f a b)) zipped)))

(defn- leapfrog-iter [epsilon grad [Rs Xs] t]
  "A single iteration of the leapfrog ingration process. See the book
  for more details."
  (let [Xt-1 (get Xs (- t 1))
        Rt-half (get Rs (- t 1/2))

        Xs' (assoc Xs t (vector-op + Xt-1 (scalar-vector-op * epsilon Rt-half)))
        Rs' (assoc Rs (+ t 1/2) (vector-op - Rt-half (scalar-vector-op * epsilon (grad (get Xs' t)))))]

    [Rs' Xs']))

(defn- leapfrog [xs R0 T epsilon {args :args :as potential-gradient} project]
  "Performs leapfrog integration of the trajectory the of our
  exploration over the curve being explored. `xs` is a set of random
  variable assignments; `R0` is the momentum, as drawn from a MVN. `T`
  and `epsilon` are parameters of the algorithm. `potential-gradient`
  is a function that computes the gradient of the potential energy of
  the system. Finally, `project` is a helper function that produces a
  sequence of values for random-variables given a map of assignments,
  as produced by the gradient function."
  (let [grad #(project (apply-gradient potential-gradient %))

        Xs {0 (project xs)}
        Rs {1/2 (vector-op - R0 (scalar-vector-op * (* 0.5 epsilon) (grad (get Xs 0))))}

        leapfrog-fn (partial leapfrog-iter epsilon grad)
        [Rs' Xs'] (reduce leapfrog-fn [Rs Xs] (range 1 T))

        ;; for a friendlier presentation of this algorithm, see
        ;; Algorithm 4, page 87, of Introduction to Probabilistic
        ;; Programming
        Xt (vector-op + (get Xs' (- T 1)) (scalar-vector-op * epsilon (get Rs' (- T 1/2))))
        Rt (vector-op - (get Rs' (- T 1/2)) (scalar-vector-op * (* 0.5 epsilon) (grad Xt)))

        ;; we manipulated random variable assignments in this function
        ;; as a sequence of values.  However, the sampling algorithm
        ;; needs to return a map from random-variable name to their
        ;; values. This function will generate the map back from a
        ;; sequence of assigned values.
        expand (fn [coll] (reduce (fn [[i m] name] [(inc i) (assoc m name (nth coll i))]) [0 {}] args))]

    ;; since the `reduce` operation above keeps track of the index in
    ;; the collection, make sure to return only the actual map
    ;; reduced.
    [(second (expand Xt)) Rt]))

(defn- hamiltonian [M potential xs rs]
  "Calculates the Hamiltonian for a system where the assignmemnts of
  random variables is `xs` and the momentum is `rs`."
  (let [;; calculate the potential energy of the system
        Ux (apply potential xs)

        ;; kinetic energy
        r-squared-over-sd (map #(/ (* % %) M) rs)
        sum-r-squared (reduce + r-squared-over-sd)
        Kr (* 0.5 sum-r-squared)]

    ;; the Hamiltonian is defined as H(X, R) = U(X) + K(R)
    (+ Ux Kr)))

(defn- hmc-step [M mvn T epsilon potential {args :args :as potential-gradient} xs]
  "Performs a single step of the Hamiltonian Monte Carlo
  algorithm. Given a set of assignments `xs` this function will
  produce the next one. See the Introduction to Probabilistic
  Programming book for a friendlier explanation of how the algorithm
  works."
  (let [;; project a map of assignments, as produced by the gradient
        ;; function, for example, into a sequence of parameters than
        ;; can be used to calculate the potential energy or its
        ;; partial derivatives.
        project (fn [assignments] (reduce (fn [coll name] (conj coll (get assignments name))) [] args))

        ;; initial momentum: sample from the Multivariate Normal
        ;; distribution.
        R (anglican/sample* mvn)

        ;; get the next set of assignments and momentum from the
        ;; leapfrog integration.
        [xs' R'] (leapfrog xs R T epsilon potential-gradient project)

        u (anglican/sample* uniform01)
        H (partial hamiltonian M potential)

        ;; calculate whether or not we should accept this set of
        ;; assignments
        exp-hamiltonian (Math/exp (- (H (project xs) R) (H (project xs') R')))]

    (if (< u exp-hamiltonian) xs' xs)))

(defn- init-hmc [{{P :P Y :Y} :G :as model} latent initial]
  "Initializes the Hamiltonian Monte Carlo sampling algorithm. Uses
  hard-coded parameters for the number of iterations used in the
  leapfrog integration (`T`); `epsilon` and the mass `M` of the system
  are also fixed. Returns the initial set of assignments to be used
  when sampling and a function that, given one set of assignments,
  produces the next."
  (let [ ;; parameters of the HMC algorithm
        T 10
        epsilon 0.01
        M 0.3
        mvn (mvn-mass-matrix (count latent) M)

        ;; generate functions to compute the potential energy of the
        ;; system at different points, as well as the gradient of the
        ;; potential energy with respect to the latent variables of
        ;; the model.
        [potential gradient] (potential-energy-gradient model latent)

        ;; the `next-fn` is just `hmc-step` partially applied with
        ;; values that remain constant during the execution of the
        ;; algorithm.
        next-fn (partial hmc-step M mvn T epsilon potential gradient)

        ;; use the first iteration of the algorithm as the initial
        ;; assignment of variables that is visible to the caller
        initial-assignments (next-fn initial)]

    [initial-assignments next-fn]))

(defn- sampling-lazy-seq [initial gen-fn]
  "Generates a lazy sequence for an initial map of
  assignments. `gen-fn` is supposed to be a function that takes a map
  of assignments, and returns an updated map of assignments as a
  result of running a single step a sampling algorithm."
  (let [next (gen-fn initial)]
    (lazy-seq (cons next (sampling-lazy-seq next gen-fn)))))

(defn perform [algo {{A :A Y :Y P :P :as graph} :G :as model}]
  {:pre [(or (= algo :gibbs) (= algo :hmc))]} ;; validate sampling algorithms
  "Performs sampling of the posterior distribution of latent variables
  represented by a graphical model. Returns a lazy sequence of samples
  from the posterior. `algo` indicates which sampling algorithm to
  use: `:gibbs` for Metropolis-within-Gibbs; or `:hmc` for Hamiltonian
  Monte Carlo."
  (let [latent (latent-vars graph)

        ;; initial random-variable assignment is drawn from the prior
        ;; ditributions
        prior-samples (operations/sample-from-prior model)
        xs (reduce (fn [m v] (assoc m v (get prior-samples v))) {} latent)

        init-fn (cond
                  (= algo :gibbs) init-gibbs
                  (= algo :hmc) init-hmc)

        [initial gen-fn] (init-fn model latent xs)]

    (sampling-lazy-seq initial gen-fn)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Temporary code -- delete after marking is done ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- path->model [path]
  (let [fd (clojure.java.io/reader path)
        stream (java.io.PushbackReader. fd)]
    (->> stream
         ast/read-source
         foppl.validation/perform
         foppl.desugar/perform
         foppl.scope/perform
         foppl.graphical/perform)))

(defn test-p1 [algo]
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p1.foppl")
        samples-seq (perform algo model)
        mu (:name (:E model))
        burn-in (take 10000 samples-seq)
        samples (take 50000 samples-seq)
        values (map (fn [m] (get m mu)) samples)
        mean (anglican/mean values)]
    (println "Expected value of mu:" mean)))

(defn test-p2 [algo]
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p2.foppl")
        samples-seq (perform algo model)
        [slope bias] (map :name (:args (:E model)))
        samples (take 50000 samples-seq)

        slope-values (map (fn [m] (get m slope)) samples)
        slope-mean (anglican/mean slope-values)

        bias-values (map (fn [m] (get m bias)) samples)
        bias-mean (anglican/mean bias-values)]
    (println "Expected value of slope:" slope-mean)
    (println "Expected value of bias:" bias-mean)))

(defn test-p3 [algo]
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p3.foppl")
        samples-seq (perform algo model)

        ;; destructure deterministic expression to get name of the
        ;; list of random variables in the vector
        {[{[{vector-args :args}] :args} *others] :args} (:E model)
        vector-args-names (map :name vector-args)
        first-name (first vector-args-names)
        second-name (second vector-args-names)

        samples (take 10000 samples-seq)
        are-equal-values (map (fn [m] (= (get m first-name) (get m second-name))) samples)
        prob-equal-values (/ (count (filter identity are-equal-values)) (count samples))]

    (println "Probability of being in the same cluster:" (float prob-equal-values))))

(defn test-p4 [algo]
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p4.foppl")
        samples-seq (perform algo model)

        ;; destructure deterministic expression to get name of
        ;; 'is-cloudy' and the two related branches of the conditional
        {{[{is-cloudy :name} _] :args} :predicate {then :name} :then {else :name} :else} (:E model)

        samples (take 200000 samples-seq)
        is-raining-values (map (fn [m] (if (get m is-cloudy) (get m then) (get m else))) samples)
        prob-is-raining (/ (count (filter identity is-raining-values)) (count samples))]

    (println "Probability that it is raining:" (float prob-is-raining))))

(defn test-p5 [algo]
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p5.foppl")
        samples-seq (perform algo model)

        ;; destructure deterministic expression to get name of
        ;; 'is-cloudy' and the two related branches of the conditional
        {[{x :name} {y :name}] :args} (:E model)

        _ (take 10000 samples-seq)
        samples (take 100000 samples-seq)
        x-values (map (fn [m] (get m x)) samples)
        y-values (map (fn [m] (get m y)) samples)]

    (println "Mean x:" (anglican/mean x-values))
    (println "Variance x", (Math/pow (anglican/std x-values) 2))
    (println "Mean y:" (anglican/mean y-values))
    (println "Variance y:" (Math/pow (anglican/std y-values) 2))))
