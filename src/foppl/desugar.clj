(ns foppl.desugar
  "Desugars a FOPPL program"
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast fn-application definition local-binding if-cond sample observe program])
  (:require [foppl.utils :as utils]))

(defrecord vector-desugar-visitor [])

(defn- accept-coll [coll v]
  (let [desugar (fn [n] (accept n v))]
    (map desugar coll)))

(extend-type vector-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v literal-vector]
    (ast/fn-application. 'vector (accept-coll (:es literal-vector) v)))

  (visit-definition [v {name :name args :args e :e}]
    (ast/definition. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (mapcat desugar-pair pairs)]
      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

(defn perform [{defs :defs e :e}]
  (let [visitor (vector-desugar-visitor.)
        desugar (fn [n] (accept n visitor))]
    (ast/program. (map desugar defs) (desugar e))))
