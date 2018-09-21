(ns foppl.graphical
  "Graphical model backend. This module is responsible for generating
  a graphical model representation of a FOPPL program given a desugared
  AST data structure."
  (:require [clojure.set :as set])
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast constant variable fn-application definition local-binding foreach loops if-cond sample observe program])
  (:require [foppl.utils :as utils]))

;; lists all of the known/expected distribution function supported by FOPPL.
;; This list of distributionns was extracted from those supported by Anglican,
;; on which this implementation depends.
(def ^:private distributions
  ['bernoulli
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
   ])

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
    (G. (set/union vertices) (set/union edges) (merge probabilities) (merge observations))))

(defn- accept-coll [coll v]
  "Given a collection of AST nodes and a node visitor, this function will apply
  the visitor to all elements of the collection."
  (let [perform (fn [n] (accept n v))]
    (doall (map perform coll))))

;; an AST visitor that performs substitution of a variable of the given
;; name for expression 'e' in some target expression
(defrecord substitution-visitor [name e])

(extend-type substitution-visitor
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during codegen"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during codegen"))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during codegen"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during codegen"))

  (visit-constant [_ c]
    c)

  (visit-variable [{name :name e :e} {var-name :name :as var}]
    (if (= name var-name) e var))

  (visit-definition [v {name :name args :args e :e}]
    (utils/foppl-error "function definitions should not be inside variable substitution"))

  (visit-local-binding [{name :name :as v} {bindings :bindings es :es :as local-binding}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-var (first bindings)
          bound-name (:name bound-var)
          bound-val (last bindings)
          new-bindings [bound-var (accept bound-val v)]
          es (if (= name bound-name) es (accept-coll es v))]
      (ast/local-binding. new-bindings es)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

(defn- substitute [name e target]
  "Substitutes 'name' for expression 'e' in expression 'target'.
  Returns a modified AST subtree."
  (let [visitor (substitution-visitor. name e)]
    (accept target visitor)))

;; This visitor is responsible for finding out all the free variables
;; in an expression, given a set of variables known to be bound.
(defrecord fv-visitor [bound])

;; traverses the AST starting at expressio  'e' adding 'name'
;; to the list of variables known to be bound.
(defn- accept-with-bound-name [name e {bound :bound}]
  (let [visitor (fv-visitor. (set/union bound #{name}))]
    (accept e visitor)))

(extend-type fv-visitor
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during free-variable visit"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during free-variable visit"))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during free-variable visit"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during free-variable visit"))

  (visit-constant [_ c]
    #{})

  (visit-variable [{bound :bound} {name :name}]
    (if (contains? bound name)
      #{}
      #{name}))

  (visit-definition [v {name :name args :args e :e}]
    (utils/foppl-error "function definitions should not be in FOPPL expressions"))

  (visit-local-binding [{name :name :as v} {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-var (first bindings)
          bound-name (:name bound-var)
          bound-val (last bindings)
          e (first es)]
      (set/union (accept bound-val v) (accept-with-bound-name bound-name e v))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (set/union (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {args :args}]
    (apply set/union (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (accept dist v))

  (visit-observe [v {dist :dist val :val}]
    (set/union (accept dist v) (accept val v)))
  )

(defn- fv [e]
  "Returns a set of free variables contained in expression 'e'"
  (let [visitor (fv-visitor. #{})]
    (accept e visitor)))

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

  (visit-constant [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))

  (visit-variable [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))

  (visit-definition [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))

  (visit-local-binding [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [f2 (accept then v)
          f3 (accept else v)]
      (ast/if-cond. predicate f2 f3)))

  (visit-fn-application [{random-v :random-v} {name :name args :args}]
    (if (contains? distributions name)
      (ast/fn-application. name (cons random-v args))
      (utils/foppl-error (str "Unknown distribution: " name))))

  (visit-sample [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))

  (visit-observe [_ _]
    (utils/foppl-error "Not a distribution object: Score(E, v) = ⊥"))
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

(extend-type graphical-model-backend
  ast/visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during codegen"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during codegen"))

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
          target-e (substitute bound-name deterministic-e1 e2)

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
    (let [;; first, recursively translate the predicate to a model with a graph and
          ;; a resulting deterministic expression
          g1 (accept predicate v)
          deterministic-predicate (:E g1)
          graph-1 (:G g1)

          ;; to translate the 'then' clause of the if expression, we need
          ;; to conjoin phi with the deterministic predicate, and recursively
          ;; visit that expression
          then-control-flow (if (= phi true) deterministic-predicate (ast/fn-application. 'and [phi deterministic-predicate]))
          g2 (accept-with-control-flow then-control-flow then v)
          deterministic-then (:E g2)
          graph-2 (:G g2)

          ;; similarly, to translate the 'else' clase of the if expression, we need
          ;; to conjoin phi with the negation of the deterministic predicate and
          ;; recursively visit that expression
          not-predicate (ast/fn-application. 'not deterministic-predicate)
          else-control-flow (if (= phi true) not-predicate (ast/fn-application. 'and [phi not-predicate]))
          g3 (accept-with-control-flow else-control-flow else v)
          deterministic-else (:E g3)
          graph-3 (:G g3)]

      ;; finally, the resulting model is the merge of all graphs generated above, with deterministic
      ;; expressinon represented by an if expression where each of e1, e2, e3 are replaced by
      ;; their deterministic counterparts
      (model. (merge-graphs graph-1 graph-2 graph-3) (ast/if-cond. deterministic-predicate deterministic-then deterministic-else))))

  (visit-fn-application [{env :environment :as v} {name :name args :args}]
    )

  (visit-sample [v {dist :dist}]
    (let [;; step one: generate a graph + deterministic expression for the
          ;; distribution expression
          graphical-dist (accept dist v)
          graph (:G graphical-dist)

          ;; destructure the graph obtained in each of its
          ;; constituents
          deterministic-dist (:E graphical-dist)
          V (:V graph)
          A (:A graph)
          P (:P graph)
          Y (:Y graph)

          ;; generate a fresh symbol
          fresh (ast/fresh-sym "sample")

          ;; find the set of free variables of the deterministic
          ;; expression representing the distribution
          free-vars (fv deterministic-dist)

          ;; find the probability density function of the distribution
          ;; being sampled, given by the SCORE function
          pdf (score deterministic-dist fresh)

          ;; for each of the free variables in the distribution,
          ;; create an edge between it and the fresh variable representing
          ;; this random variable
          new-edges (set (map (fn [fv] [fv, fresh]) free-vars))

          ;; the resulting graph adds the fresh variable to the set
          ;; of vertices, the new edges computed above, and a mapping
          ;; between the fresh variable and the pdf function.
          result-graph (G. (set/union V (set fresh)) (set/union A new-edges) (merge P {fresh pdf}) Y)]

      ;; the deterministic expression of a sample expression is a variable with
      ;; the fresh name generated in the bindings above
      (model. result-graph (ast/variable. fresh))))

  (visit-observe [v {dist :dist val :val}]
    )
  )


(defn perform [{defs :defs e :e}]
  (let [visitor (graphical-model-backend. defs true)]
    (accept e visitor)))
