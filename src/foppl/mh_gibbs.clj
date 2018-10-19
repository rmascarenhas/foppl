(ns foppl.mh_gibbs
  "Implements the Metropolis-within-Gibbs algorithm for the sampling of
  the posterior of the distribution represented by a graphical model."
  (:require [clojure.set :as set]
            [clojure.edn :as edn]
            [anglican.runtime :as anglican]
            [foppl.ast :as ast :refer [accept]]
            [foppl.eval :as eval]
            [foppl.formatter :as formatter]
            [foppl.operations :as operations]
            [foppl.toposort :as toposort]
            [foppl.utils :as utils])
  (:import [foppl.ast constant variable if-cond fn-application definition]))

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

  (visit-definition [_ defnition]
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
    (utils/foppl-error "Not a distribution object: Score(sample, v) = ⊥"))

  (visit-observe [_ _]
    (utils/foppl-error "Not a distribution object: Score(observe, v) = ⊥"))
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
        u (rand)]

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

(defn- gibbs-lazy-seq [initial gen-fn]
  "Generates a lazy sequence for an initial map of
  assignments. `gen-fn` is supposed to be a function that takes a map
  of assignments, and returns an updated map of assignments as a
  result of running a single step of the Gibbs algorithm."
  (let [next (gen-fn initial)]
    (lazy-seq (cons next (gibbs-lazy-seq next gen-fn)))))

(defn perform [{{A :A Y :Y P :P :as graph} :G :as model}]
  "Performs sampling of the posterior distribution of latent variables
  represented by a graphical model. Returns a lazy sequence of samples
  from the posterior."
  (let [latent (latent-vars graph)

        ;; helper function to create maps from latent variables to
        ;; some value
        with-latent (partial zipmap latent)

        ;; extracts distribution AST node from a link function (which
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
        proposals (with-latent (map make-lambda link-fns))

        ;; initial random-variable assignment is drawn from the prior
        ;; ditributions
        prior-samples (operations/sample-from-prior model)
        xs (reduce (fn [m v] (assoc m v (get prior-samples v))) {} latent)

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
        {burned-in :xs} (gibbs 2000 xs)

        ;; the `gibbs` helper function defined above is a lot more
        ;; general and is able to run `n` gibbs steps. However, in
        ;; order to generate our lazy sequence, we write a wrapper for
        ;; it that, given a map of assignments, produces a new map of
        ;; assignments as a result of running a single gibbs step
        next-sample (fn [xs] (:xs (gibbs 1 xs)))]

    (gibbs-lazy-seq burned-in next-sample)))


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

(defn test-p1 []
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p1.foppl")
        samples-seq (perform model)
        mu (:name (:E model))
        samples (take 200000 samples-seq)
        values (map (fn [m] (get m mu)) samples)
        mean (anglican/mean values)]
    (println "Expected value of mu:" mean)))

(defn test-p2 []
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p2.foppl")
        samples-seq (perform model)
        [slope bias] (map :name (:args (:E model)))
        samples (take 200000 samples-seq)

        slope-values (map (fn [m] (get m slope)) samples)
        slope-mean (anglican/mean slope-values)

        bias-values (map (fn [m] (get m bias)) samples)
        bias-mean (anglican/mean bias-values)]
    (println "Expected value of slope:" slope-mean)
    (println "Expected value of bias:" bias-mean)))

(defn test-p3 []
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p3.foppl")
        samples-seq (perform model)

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

(defn test-p4 []
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p4.foppl")
        samples-seq (perform model)

        ;; destructure deterministic expression to get name of
        ;; 'is-cloudy' and the two related branches of the conditional
        {{[{is-cloudy :name} _] :args} :predicate {then :name} :then {else :name} :else} (:E model)

        samples (take 200000 samples-seq)
        is-raining-values (map (fn [m] (if (get m is-cloudy) (get m then) (get m else))) samples)
        prob-is-raining (/ (count (filter identity is-raining-values)) (count samples))]

    (println "Probability that it is raining:" (float prob-is-raining))))

(defn test-p5 []
  (let [model (path->model "/home/rmc/Documents/canada/ubc/cw/2018.fall/539/foppl/resources/examples/gibbs/p5.foppl")
        samples-seq (perform model)

        ;; destructure deterministic expression to get name of
        ;; 'is-cloudy' and the two related branches of the conditional
        {[{x :name} {y :name}] :args} (:E model)

        samples (take 2000 samples-seq)
        x-values (map (fn [m] (get m x)) samples)
        y-values (map (fn [m] (get m y)) samples)]

    (println "Mean x:" (anglican/mean x-values))
    (println "Variance x", (Math/pow (anglican/std x-values) 2))
    (println "Mean y:" (anglican/mean y-values))
    (println "Variance y:" (Math/pow (anglican/std y-values) 2))))
