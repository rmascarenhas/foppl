(ns foppl.desugar
  "Desugars a FOPPL program. See documentation for each of the AST visitors
  defined in this namespace to find out each desugaring step applied."
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast variable fn-application definition local-binding if-cond sample observe program])
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

;; let forms are allowed to contain multiple bindings at the same time. In addition,
;; multiple expressions can be passed to be "body" of a 'let' expression. However,
;; both of these features are syntactic sugar on top of a more primitive 'let'
;; construct which allows a single bound name and a single expression. This visitor
;; traverses the AST and rewrites 'let' forms with multiple bindings and expressions
;; to 'let' forms with a single bound name and expression.
(defrecord let-form-desugar-visitor [])

(extend-type let-form-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [_ literal-vector]
    (utils/ice "Literal vectors should not exist when desugaring 'let' forms"))

  (visit-literal-map [_ literal-map]
    (utils/ice "Literal maps should not exist when desugaring 'let' forms"))

  (visit-definition [v {name :name args :args e :e}]
    (ast/definition. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(even? (count bindings)) (> (count bindings) 0) (> (count es) 0)]}

    (let [pairs (partition 2 bindings)
          bound (count pairs)
          first-bind (first pairs)
          rest-binds (rest (rest bindings))
          num-es (count es)
          variable (fn [name] (ast/variable. name))]
      (cond
        ;; if there is only one bound name, the bindings are going to remain the same,
        ;; but the enclosed expressions may have to change to extra 'let' bindings
        ;; (binding the symbol "_") to the remaining expressions when there is
        ;; more than one
        (= bound 1) (ast/local-binding. bindings (cond
                                                   (= num-es 1) (accept-coll es v)
                                                   (> num-es 1) [(accept (ast/local-binding.
                                                                          [(variable '_) (first es)] (rest es)) v)]))

        ;; if there is more than one binding in the 'let' form, transform this node
        ;; into a binding of the first bound name, and recursively traverse the remaining
        ;; bindings.
        (> bound 1) (ast/local-binding. first-bind [(accept (ast/local-binding. rest-binds es) v)]))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

(defn- apply-desugaring [v {defs :defs e :e}]
  (let [desugar (fn [n] (accept n v))]
    (ast/program. (map desugar defs) (desugar e))))

(defn perform [program]
  "Performs desugaring of a program. Returns a ast/program record containing
  the expanded AST containing only the FOPPL's core language."

  ;; visitors that should operate on the AST to iteratively
  ;; remove sugar
  (let [visitors [(data-structure-desugar-visitor.)
                  (let-form-desugar-visitor.)]

        curry (fn [v] (partial apply-desugaring v))
        curried (map curry visitors)

        ;; since the 'visitor' definition was listed in the
        ;; order in which they should be applied, for ease
        ;; of understanding.
        desugar (apply comp (reverse curried))]

    (desugar program)))
