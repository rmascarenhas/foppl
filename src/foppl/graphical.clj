(ns foppl.graphical
  "Graphical model backend. This module is responsible for generating
  a graphical model representation of a FOPPL program given a desugared
  AST data structure."
  (:require [clojure.set :as set])
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast constant variable fn-application definition local-binding foreach loops if-cond sample observe program])
  (:require [foppl.utils :as utils]))

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
  (G. #{} #{} {} {}))

(defn- merge-graphs [{V1 :V A1 :A P1 :P Y1 :Y} {V2 :V A2 :A P2 :P Y2 :Y}]
  (G. (set/union V1 V2) (set/union A1 A2) (merge P1 P2) (merge Y1 Y2)))

(defn- accept-coll [coll v]
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
  (let [visitor (substitution-visitor. name e)]
    (accept target visitor)))

;; represents a graphical model, where:
;;     - G is a graph representing the FOPPL's program structure
;;     - E is the FOPPL program's deterministic expression
(defrecord model [G E])

(defrecord graphical-model-backend [])

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
    )

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-name (:name (first bindings))
          e1 (last bindings)
          e2 (first es)
          g1 (accept e1 v)
          deterministic-e1 (:E g1)
          target-e (substitute)
          g2 (accept target-e v)
          graph-1 (:G g1)
          graph-2 (:G g2)
          deterministic-e2 (:E g2)]
      (model. (merge-graphs graph-1 graph-2) deterministic-e2)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    )

  (visit-fn-application [{env :environment :as v} {name :name args :args}]
    )

  (visit-sample [v {dist :dist}]
    )

  (visit-observe [v {dist :dist val :val}]
    )
  )

(defn perform [{defs :defs e :e}]
  (let [visitor (graphical-model-backend.)]
    (accept e visitor)))
