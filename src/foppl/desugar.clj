(ns foppl.desugar
  "Desugars a FOPPL program. See documentation for each of the AST visitors
  defined in this namespace to find out each desugaring step applied."
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast fn-application definition local-binding if-cond sample observe program])
  (:require [foppl.utils :as utils]))

;; the data structure desugaring visitor translates every literal array ([e1, e2, ...]) to
;; a function application of 'vector'. In addition, it also transforms every literal map
;; representation ({e1 e2 e3 e4 ...}) to an application of 'hash-map'.
(defrecord data-structure-desugar-visitor [])

(defn- accept-coll [coll v]
  "Desugars every element in a collection, returning a mapped collection
  of desugared nodes"
  (let [desugar (fn [n] (accept n v))]
    (map desugar coll)))

(extend-type data-structure-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v literal-vector]
    (ast/fn-application. 'vector (accept-coll (:es literal-vector) v)))

  (visit-literal-map [v literal-map]
    (ast/fn-application. 'hash-map (accept-coll (:es literal-map) v)))

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
  "Performs desugaring of a program. Returns a ast/program record containing
  the expanded AST containing only the FOPPL's core language."
  (let [visitor (data-structure-desugar-visitor.)
        desugar (fn [n] (accept n visitor))]
    (ast/program. (map desugar defs) (desugar e))))
