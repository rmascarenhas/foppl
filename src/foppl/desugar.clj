(ns foppl.desugar
  "Desugars a FOPPL program. See documentation for each of the AST visitors
  defined in this namespace to find out each desugaring step applied."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.utils :as utils])
  (:import [foppl.ast constant variable fn-application procedure lambda local-binding
            foreach loops if-cond sample observe program]))

;; the data structure desugaring visitor translates every literal array ([e1, e2, ...]) to
;; a function application of 'vector'. In addition, it also transforms every literal map
;; representation ({e1 e2 e3 e4 ...}) to an application of 'hash-map'.
(defrecord data-structure-desugar-visitor [])

(defn- accept-coll [coll v]
  "Desugars every element in a collection, returning a mapped collection
  of desugared nodes"
  (let [desugar (fn [n] (accept n v))]
    (doall (map desugar coll))))

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

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (doall (mapcat desugar-pair pairs))]
      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (doall (mapcat desugar-pair pairs))]
      (ast/foreach. c desugared-bindings (accept-coll es v))))

  (visit-loop [v {c :c e :e f :f es :es}]
    (ast/loops. (accept c v) (accept e v) f (accept-coll es v)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v))))

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

  (visit-foreach [_ foreach]
    (utils/ice "foreach should have been desugared before processing 'let' forms"))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(even? (count bindings)) (> (count es) 0)]}

    (let [pairs (partition 2 bindings)
          bound (count pairs)
          is-empty (empty? pairs)

          ;; first name-value pair of in the local binding
          first-bind (first pairs)

          ;; recursively traverse the AST of the expression being bound to
          ;; the first name. Only this pair needs to be traversed at this point
          ;; since, if this local binding binds more than one name, a recursive
          ;; call will call this function in the subsequent bindings.
          first-expanded (when-not is-empty [(first first-bind) (accept (last first-bind) v)])

          rest-binds (rest (rest bindings))
          num-es (count es)
          variable (fn [name] (ast/variable. name))]
      (cond
        ;; on an empty 'let' expression (most often result of a 'foreach' construct without
        ;; any bound names), behavior depends on the number of expressions that follow.
        ;; 'let [] e' is translated to e; whereas 'let [] e1 e2' is translated to
        ;; 'let [_ e1] e2'
        (= bound 0) (cond
                      (= num-es 1) (accept (first es) v)
                      (> num-es 1) (accept (ast/local-binding. [(variable '_) (accept (first es) v)] (rest es)) v))

        ;; if there is only one bound name, the bindings are going to remain the same,
        ;; but the enclosed expressions may have to change to extra 'let' bindings
        ;; (binding the symbol "_") to the remaining expressions when there is
        ;; more than one
        (= bound 1) (ast/local-binding. first-expanded (cond
                                                         (= num-es 1) (accept-coll es v)
                                                         (> num-es 1) [(accept
                                                                        (ast/local-binding.
                                                                         [(variable '_) (accept (first es) v)] (rest es)) v)]))

        ;; if there is more than one binding in the 'let' form, transform this node
        ;; into a binding of the first bound name, and recursively traverse the remaining
        ;; bindings.
        (> bound 1) (ast/local-binding. first-expanded [(accept (ast/local-binding. rest-binds es) v)]))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

;; The 'foreach' construct allows a FOPPL program to iterate over collections
;; of a fixed, constant size. 'foreach' is desugared to a series of local binding
;; statements where each element of each collection is applied to every expression
;; in the body consecutively.
(defrecord foreach-desugar-visitor [])

(extend-type foreach-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v literal-vector]
    (accept-coll (:es literal-vector) v))

  (visit-literal-map [v literal-map]
    (accept-coll (:es literal-map) v))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (doall (mapcat desugar-pair pairs))]
      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (let [iters (:n c)
          pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (doall (map desugar-pair pairs))

          ;; builds a list of bindings for the bound names at index 'n'.
          ;; Uses the 'get' function to retrieve element at nth position
          ;; of a collection
          get-fn (fn [n] (fn [[name val]] [name (ast/fn-application. 'get [val (ast/constant. n)])]))
          build-bindings (fn [n] (mapcat (get-fn n) desugared-bindings))

          ;; creates a local binding with multiple bound names for an index 'n'.
          ;; This assumes that the let-form-desugaring process will process the
          ;; AST *after* this visitor.
          desugared-es (accept-coll es v)
          bindings-at (fn [n] (ast/local-binding. (build-bindings n) desugared-es))]

      (ast/fn-application. 'vector (doall (map bindings-at (range iters))))))

  (visit-loop [v {c :c e :e f :f es :es}]
    (ast/loops. (accept c v) (accept e v) f (accept-coll es v)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

;; desugars 'loop' forms to a series of bindings for each expression.
;; See the book for details of how the translation of 'loop' expressions
;; is performed.
(defrecord loop-desugar-visitor [])

(extend-type loop-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v literal-vector]
    (accept-coll (:es literal-vector) v))

  (visit-literal-map [v literal-map]
    (accept-coll (:es literal-map) v))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (doall (mapcat desugar-pair pairs))]
      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (ast/foreach. (accept c v) (accept-coll bindings v) (accept-coll es v)))

  (visit-loop [v {c :c e :e f :f es :es}]
    (let [iters (:n c) ;; number of iterations in this loop

          ;; helper function -- creates a variable AST node given a name
          variable (fn [name] (ast/variable. name))

          ;; creates a variable -> expression pair given an expression (recursively
          ;; transforming the expression). Use the "a-" prefix for similarity with
          ;; the translation form used in the book.
          create-binding (fn [e] [(variable (ast/fresh-sym "a")) (accept e v)])

          ;; creates a list of bindings for the expressions passed to the 'loop'
          ;; construct
          bindings (doall (mapcat create-binding es))

          ;; the variables bound to the expressions passed to 'loop'
          bound-vars (map first (partition 2 bindings))

          ;; creates variable nodes for the nested local bindings to be used
          ;; in each step of the computation
          accum-vars (map (fn [_] (variable (ast/fresh-sym "v"))) (range iters))

          ;; generates a name -> expression pair for the cumulative operations of a loop.
          ;; If we are at index 0, the initial expression given is used. Otherwise, the
          ;; name used for the previous binding is fetched and passed to the function 'f'.
          accum-binding-at (fn [n] (let [name (nth accum-vars n)
                                        current (cond
                                                  (= n 0) (accept e v)
                                                  :else (nth accum-vars (dec n)))
                                        args (cons (ast/constant. n) (cons current bound-vars))]
                                    [name (ast/fn-application. f args)]))

          ;; generates a list of bindings according to the constant number of
          ;; iterations passed to 'loop'.
          accum-bindings (doall (mapcat accum-binding-at (range iters)))

          ;; Variable used in the last cumulative binding. This is the return value of
          ;; the entire expression
          last-bound-name (last accum-vars)

          ;; the local binding for the cumulative operations
          accum [(ast/local-binding. accum-bindings [last-bound-name])]]

      ;; Note: this returns a local binding with multiple bound names. As a consequence,
      ;; it assumes that the let transformation visitor must be applied *after* this visitor
      ;; processes the AST.
      (ast/local-binding. bindings accum)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v)))
  )

;; underscores ('_) are used in FOPPL programs (and in other desugaring steps) to
;; represent unnamed variables. This visitor traverses the AST and replaces every
;; occurrence of an underscore (in function definitions and local bindings) with
;; a fresh name
(defrecord underscore-desugar-visitor [])

(extend-type underscore-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ {name :name :as variable}]
    (if (= name '_)
      (ast/variable. (ast/fresh-sym))
      variable))

  (visit-literal-vector [v literal-vector]
    (accept-coll (:es literal-vector) v))

  (visit-literal-map [v literal-map]
    (accept-coll (:es literal-map) v))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name (accept-coll args v) (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name (accept-coll args v) (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          desugar-pair (fn [[name e]] [(accept name v) (accept e v)])
          desugared-bindings (doall (mapcat desugar-pair pairs))]
      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (ast/foreach. (accept c v) (accept-coll bindings v) (accept-coll es v)))

  (visit-loop [v {c :c e :e f :f es :es}]
    (ast/loops. c (accept e v) f (accept-coll es v)))

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
  ;; remove sugar (visitors operate on the AST in the order
  ;; listed below)
  (let [visitors [(data-structure-desugar-visitor.)
                  (foreach-desugar-visitor.)
                  (loop-desugar-visitor.)
                  (let-form-desugar-visitor.)
                  (underscore-desugar-visitor.)]
        curry (fn [v] (partial apply-desugaring v))
        curried (map curry visitors)
        desugar (apply comp (reverse curried))]

    (desugar program)))
