(ns foppl.graphical
  "Graphical model backend. This module is responsible for generating
  a graphical model representation of a FOPPL program given a desugared
  AST data structure."
  (:require [clojure.set :as set]
            [clojure.string :as s]
            [foppl.ast :as ast :refer [accept]]
            [foppl.eval :as eval]
            [foppl.formatter :as formatter]
            [foppl.utils :as utils])
  (:import [foppl.ast constant variable literal-vector literal-map fn-application definition
            local-binding foreach loops if-cond sample observe program]))

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

;; represents a graph, where:
;;     - V is the set of vertices (random variables) of the graph
;;     - A is the set of edges and is a subset of V x V
;;     - P is a map from vertices to a deterministic expression that
;;       computes its density (mass) function
;;     - Y is a partial map from vertices to observed variables. Each
;;       map entry contains a pair <E, ϕ> of a deterministic expression
;;       and a predicate that determines whether the observation is in
;;       the control flow path
(defrecord G [V A P Y])

(defn- empty-graph []
  "Generates a new graph with no vertices, edges, random variables
  or observations."
  (G. #{} #{} {} {}))

(defn- merge-graphs [& graphs]
  "Merges an arbitrary number of graphs, and returns a new graph
  as a result of the merge."
  (let [vertices (map :V graphs)
        edges (map :A graphs)
        probabilities (map :P graphs)
        observations (map :Y graphs)]
    (G. (apply set/union vertices) (apply set/union edges) (apply merge probabilities) (apply merge observations))))

(defn- accept-coll [coll v]
  "Given a collection of AST nodes and a node visitor, this function will apply
  the visitor to all elements of the collection."
  (let [perform (fn [n] (accept n v))]
    (doall (map perform coll))))

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

;; The score visitor returns an AST node that corresponds to the SCORE function
;; (as described in the book) for a certain AST node. Score functions are based
;; on a random variable generated when sampling or observing a distribution.
(defrecord score-visitor [random-v])

(extend-type score-visitor
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during expression scoring"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during expression scoring"))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during expression scoring"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during expression scoring"))

  (visit-constant [{random-v :random-v} {c :n :as constant}]
    (let [class-c (str (class c))
          anglican-dist? (re-matches #".*anglican.runtime.(.*)-distribution" class-c)
          dirac-dist? (re-matches #".*foppl.primitives.dirac-distribution" class-c)
          dist? (or anglican-dist? dirac-dist?)]
      (cond
        dist? (ast/fn-application. 'anglican.runtime/observe* [constant random-v])
        (nil? c) constant
        :else (utils/foppl-error "Not a distribution object: Score(Constant, v) = ⊥"))))

  (visit-variable [_ _]
    (utils/foppl-error "Not a distribution object: Score(Variable, v) = ⊥"))

  (visit-definition [_ _]
    (utils/foppl-error "Not a distribution object: Score(defn, v) = ⊥"))

  (visit-local-binding [_ _]
    (utils/foppl-error "Not a distribution object: Score(let, v) = ⊥"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [f2 (accept then v)
          f3 (accept else v)]
      (ast/if-cond. predicate f2 f3)))

  (visit-fn-application [{random-v :random-v} {name :name args :args :as fn-application}]
    (let [qualify-v (anglican-qualify-visitor.)
          qualified-fn (accept fn-application qualify-v)]
      (ast/fn-application. 'anglican.runtime/observe* [qualified-fn random-v])))

  (visit-sample [_ _]
    (utils/foppl-error "Not a distribution object: Score(sample, v) = ⊥"))

  (visit-observe [_ _]
    (utils/foppl-error "Not a distribution object: Score(observe, v) = ⊥"))
  )

(defn- score [e random-v]
  (let [visitor (score-visitor. random-v)]
    (accept e visitor)))

;; represents a graphical model, where:
;;     - G is a graph representing the FOPPL's program structure
;;     - E is the FOPPL program's deterministic expression
(defrecord model [G E])

;; this visitor is responsible for calculating a graphical model for certain
;; expression given a context of user-defined procedures (rho) and a control-flow
;; predicate (phi).
(defrecord graphical-model-backend [rho phi])

;; given a predicate 'control-flow' and an AST node 'n', this function will
;; calculate the graphical model of the subtree rooted at 'n' adding the
;; predicate to phi
(defn- accept-with-control-flow [control-flow n {rho :rho}]
  (let [visitor (graphical-model-backend. rho control-flow)]
    (accept n visitor)))

(defn- accept-user-defined [name args {rho :rho :as v}]
  "Given a user-defined function with a given 'name' and arguments 'args',
  this will calculate the corresponding graphical model. First, every formal
  parameter is substituted by the arguments passed, and then a graphical model
  is generated based on the resulting expression."
  (let [ ;; construct a hash-map indexing <function name> -> <AST node>
        indexed (reduce merge {} (map (fn [f] {(:name f) f}) rho))

        ;; get the AST node corresponding to the user-defined function being applied
        proc (get indexed name)
        e (:e proc)

        ;; list of formal parameters of the user-defined function
        bound-names (map :name (:args proc))

        ;; builds an index of <formal parameter> -> <index in 'args'>
        args-indices (reduce merge {} (map-indexed (fn [i, name] {name i}) bound-names))

        ;; given a parameter name, this function will return the expression given
        ;; in 'args' for it, allowing formal parameters to be substituted by the
        ;; actual parameters given (as 'args' to this function)
        expression-for (fn [name] (nth args (get args-indices name)))

        ;; the target expression from which a graphical model is going to be
        ;; extracted is reduced from the list of formal parameters, by
        ;; successively performing substituion
        target-e (reduce (fn [reduced, name] (ast/substitute name (expression-for name) reduced)) e bound-names)]

    ;; generate graphical model for the target expression with every parameter
    ;; substituted
    (accept target-e v)))

(extend-type graphical-model-backend
  ast/visitor

  (visit-literal-vector [_ literal-vector]
    (model. (empty-graph) literal-vector))

  (visit-literal-map [_ literal-map]
    (model. (empty-graph) literal-map))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during codegen"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during codegen"))

  (visit-constant [v c]
    (model. (empty-graph) c))

  (visit-variable [v var]
    (model. (empty-graph) var))

  (visit-definition [v {name :name args :args e :e}]
    (utils/ice "no function definition should be reachable from graphical model backend"))

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-name (:name (first bindings))
          e1 (last bindings)
          e2 (first es)
          g1 (accept e1 v)

          ;; let [v e1] e2
          ;; step 1: translate e1 to a graph + deterministic expression
          deterministic-e1 (:E g1)

          ;; then substitute v for the deterministic expression obtained
          ;; on the previous step in the target expression e2
          target-e (ast/substitute bound-name deterministic-e1 e2)

          ;; then translate the result of that to a graph + deterministic
          ;; resulting expression
          g2 (accept target-e v)
          graph-1 (:G g1)
          graph-2 (:G g2)
          deterministic-e2 (:E g2)]

      ;; the result is a model where the gaphs obtained are merged and
      ;; the deterministic expression is returned
      (model. (merge-graphs graph-1 graph-2) deterministic-e2)))

  (visit-if-cond [{phi :phi :as v} {predicate :predicate then :then else :else}]
    (let [ ;; first, recursively translate the predicate to a model with a graph and
          ;; a resulting deterministic expression
          g1 (accept predicate v)
          deterministic-predicate (:E g1)
          graph-1 (:G g1)

          ;; to translate the 'then' clause of the if expression, we need
          ;; to conjoin phi with the deterministic predicate, partially evaluate it,
          ;; and recursively visit that expression
          then-control-flow-e (if (= phi true) deterministic-predicate (ast/fn-application. 'and [phi deterministic-predicate]))
          then-control-flow (eval/peval then-control-flow-e)
          g2 (accept-with-control-flow then-control-flow then v)
          deterministic-then (:E g2)
          graph-2 (:G g2)

          ;; similarly, to translate the 'else' clase of the if expression, we need
          ;; to conjoin phi with the negation of the deterministic predicate, partially
          ;; evaluate it, and recursively visit that expression
          not-predicate (ast/fn-application. 'not [deterministic-predicate])
          else-control-flow-e (if (= phi true) not-predicate (ast/fn-application. 'and [phi not-predicate]))
          else-control-flow (eval/peval else-control-flow-e)
          g3 (accept-with-control-flow else-control-flow else v)
          deterministic-else (:E g3)
          graph-3 (:G g3)

          ;; the resulting expression is represented by an if expression where each of e1, e2, e3
          ;; are replaced by their deterministic counterpars (and partially evaluated)
          resulting-if-e (ast/if-cond. deterministic-predicate deterministic-then deterministic-else)
          resulting-if (eval/peval resulting-if-e)]

      ;; finally, the resulting model merges of all graphs generated above
      (model. (merge-graphs graph-1 graph-2 graph-3) resulting-if)))

  (visit-fn-application [{rho :rho :as v} {name :name args :args}]
    (let [ ;; construct graphical models for each of the arguments passed to the
          ;; function recursively
          args-gs (accept-coll args v)
          args-graphs (map :G args-gs)
          deterministic-args (map :E args-gs)

          ;; find all names given to user-defined procedures in this FOPPL program
          defined-names (set (map :name rho))
          user-defined? (contains? defined-names name)

          ;; if a program was user-defined, perform variable substitution for each
          ;; argument in the procedure's expression, and then compute the resulting
          ;; graphical model on that target expression. Otherwise, the function is
          ;; a language 'builtin' and should be uninterpreted
          {g :G e :E} (if user-defined?
                        (accept-user-defined name deterministic-args v)
                        (model. (empty-graph) (eval/peval (ast/fn-application. name deterministic-args))))

          ;; the resulting graph is the result of merging the graphs of
          ;; every argument passed to the function
          resulting-graph (apply merge-graphs (cons g args-graphs))]

      ;; the model returned contains the expression that is equivalent to a
      ;; user defined procedure, or a 'builtin' function application
      (model. resulting-graph e)))

  (visit-sample [v {dist :dist}]
    (let [ ;; step one: generate a graph + deterministic expression for the
          ;; distribution expression
          graphical-dist (accept dist v)
          graph (:G graphical-dist)

          ;; destructure the graph obtained in each of its constituents
          deterministic-dist (:E graphical-dist)
          V (:V graph)
          A (:A graph)
          P (:P graph)
          Y (:Y graph)

          ;; generate a fresh symbol
          random-v (ast/fresh-sym "sample")

          ;; find the set of free variables of the deterministic
          ;; expression representing the distribution
          free-vars (ast/free-vars deterministic-dist)

          ;; find the probability density function of the distribution
          ;; being sampled, given by the SCORE function
          pdf (score deterministic-dist (ast/variable. random-v))

          ;; for each of the free variables in the distribution,
          ;; create an edge between it and the fresh variable representing
          ;; this random variable
          new-edges (set (map (fn [fv] [fv, random-v]) free-vars))

          ;; the resulting graph adds the fresh variable to the set
          ;; of vertices, the new edges computed above, and a mapping
          ;; between the fresh variable and the pdf function.
          result-graph (G. (set/union V #{random-v}) (set/union A new-edges) (merge P {random-v pdf}) Y)]

      ;; the deterministic expression of a sample expression is a variable with
      ;; the fresh name generated in the bindings above
      (model. result-graph (ast/variable. random-v))))

  (visit-observe [{phi :phi :as v} {dist :dist val :val}]
    (let [ ;; first step: recursively determine the graph and deterministic expression
          ;; corresponding to the distribution of the observation
          g1 (accept dist v)
          graph-1 (:G g1)
          e1 (:E g1)

          ;; then recursively compute the graphical model for the observed value
          g2 (accept val v)
          graph-2 (:G g2)
          e2 (:E g2)

          ;; merge both graphs together, and destructure them into their
          ;; constituent parts
          merged-graphs (merge-graphs graph-1 graph-2)
          V (:V merged-graphs)
          A (:A merged-graphs)
          P (:P merged-graphs)
          Y (:Y merged-graphs)

          ;; create a new, fresy symbol for the random variable that will
          ;; correspond to this observation
          random-v (ast/fresh-sym "observe")

          ;; make sure the distribution expression is indeed of a distribution type
          ;; by calculating its score (which will panic in case it is not)
          f1 (score e1 (ast/variable. random-v))

          ;; make sure the density function takes into account the control flow
          ;; predicate phi
          f (if (= phi true) f1 (ast/if-cond. phi f1 (ast/constant. 1)))

          ;; let Z be the set of free variables in f excluding the fresh
          ;; variable created
          z (set/difference (ast/free-vars f) #{random-v})

          ;; validation step: ensure that the observed value has no random
          ;; variables in it (i.e., it is deterministic)
          _ (when-not (empty? (set/intersection (ast/free-vars e2) V)) (utils/foppl-error "observed value is not deterministic"))

          ;; creates a collection of mappings from free-variables to the
          ;; random variable created
          b (map (fn [free-var] [free-var, random-v]) z)

          ;; finally, the resulting graph adds the random variable created here to the
          ;; set of vertices of the graph; adds the set of edges 'b' computed above;
          ;; maps the random variable to its probability density function; and adds
          ;; the observed value to the observed expression e2
          resulting-graph (G. (set/union V #{random-v}) (set/union A (set b)) (merge P {random-v f}) (merge Y {random-v e2}))]

      ;; the model returned uses the observed expression as its result
      (model. resulting-graph e2)))
  )

(defn perform [{defs :defs e :e}]
  (let [visitor (graphical-model-backend. defs true)]
    (accept e visitor)))
