(ns foppl.hoppl
  "This module implements evaluation-based inference. It extends FOPPL
  by adding higher-order features to it: specifically, HOPPL allows
  the use of anonymous functions and recursion."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.desugar :as desugar]
            [foppl.eval :as eval]
            [foppl.utils :as utils]
            [anglican.runtime :as anglican])
  (:import [foppl.ast constant variable if-cond fn-application literal-vector
            literal-map procedure lambda local-binding sample observe program]))

(defn- accept-coll [coll v]
  "Visits a collection of AST nodes `coll` with visitor `v`."
  (let [perform (fn [n] (accept n v))]
    (map perform coll)))

;; loop-desugar-visitor is responsible for desugaring `loop` forms in HOPPL programs. Loops
;; in HOPPL are equivalent to a `let` expression which then applies the `loop-helper`
;; function (see definition in `foppl.primitives`).
(defrecord loop-desugar-visitor [])

(extend-type loop-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v {es :es}]
    (ast/literal-vector. (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (ast/literal-map. (accept-coll es v)))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)

          ;; loop desugaring is the first to be performed. Local
          ;; bindings may still include multiple bindings in a single
          ;; `let` form, so we desugar every pair.
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (mapcat desugar-pair pairs)]

      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (let [;; helper functions to create variable and constant AST nodes
          variable (fn [name] (ast/variable. name))
          constant (fn [c] (ast/constant. c))

          ;; for each expression to e1, e2, ..., en passed to `loop`,
          ;; generate a fresh symbol for it
          bound-names (repeatedly (count es) #(variable. (ast/fresh-sym)))

          ;; bind each expression to the symbols generated
          bound-es (into [] (mapcat vector bound-names es))

          ;; the `g` function is an anonymous function that is used in
          ;; the `loop-helper` function, made available by HOPPL.
          g (ast/lambda. nil
                         [(variable 'i) (variable 'w)]
                         (ast/fn-application. f (into [(variable 'i) (variable 'w)] bound-names)))

          ;; all bindings in the desugared `let` corresponding to the
          ;; HOPPL `loop`.  See the book for a better diagram of the
          ;; desugaring process.
          bindings (into [(variable 'bound) c (variable 'initial-value) e] (into bound-es [(variable 'g) g]))

          e (ast/fn-application. 'loop-helper [(constant 0) (variable 'bound) (variable 'initial-value) (variable 'g)])]

      (ast/local-binding. bindings [e])))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v))))

;; let-desugar-visitor performs desugaring of `let` expressions in the
;; HOPPL context.  `let` forms are removed altogether in HOPPL since
;; we can replace them with applications of anonymous functions:
;;
;;     (let [x v] (+ x 1))
;;
;; gets desugared to:
;;
;;     ((fn [x] (+ x 1)) v)
(defrecord let-desugar-visitor [])

(extend-type let-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v {es :es}]
    (ast/literal-vector. (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (ast/literal-map. (accept-coll es v)))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [;; the name being bound
          name (first bindings)

          ;; the value being bound
          val (accept (second bindings) v)

          ;; the expression in which `name` is bound to `val`
          e (accept (first es) v)

          ;; the function we want to apply
          lam (ast/lambda. nil [name] e)]


      ;; TODO: we are abusing of the `fn-application` AST node
      ;; here. It was originally intended to be used in the FOPPL
      ;; context where element in function position would always be a
      ;; symbol.  In HOPPL-land, it can be any expression. Ideally,
      ;; the `fn-application` node should be generalized to accept
      ;; arbitrary expressions in function position, but that requires
      ;; significant changes in the existing FOPPL source code.
      (ast/fn-application. lam [val])))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/foppl-error "loop expressions should have been desugared"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v))))

(declare to-clojure-value)

(defrecord clojure-value-visitor [env])

(extend-type clojure-value-visitor
  ast/visitor

  (visit-constant [_ {n :n}]
    n)

  (visit-variable [{env :env} {name :name}]
    (get env name))

  (visit-literal-vector [v {es :es}]
    (into [] (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (let [elements (accept-coll es v)
          to-vec (fn [coll] (into [] coll))
          partitions (map to-vec (partition 2 elements))
          map-elements (to-vec partitions)]
      (into {} map-elements)))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/foppl-error "Procedure definitions should not exist when computing Clojure value"))

  (visit-lambda [{env :env :as v} {name :name args :args e :e}]
    (fn [& params]
      (let [args-names (map :name args)
            env-extension (zipmap args-names params)]
        (to-clojure-value e (merge env env-extension)))))

  (visit-local-binding [v {bindings :bindings es :es}]
    (utils/foppl-error "Local bindings should have been removed when computing Clojure value"))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/foppl-error "loop expressions should have been desugared"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (utils/foppl-error "If conditions should have beem removed when computing Clojure value"))

  (visit-fn-application [v {name :name args :args}]
    (utils/foppl-error "Function application is not a value"))

  (visit-sample [v {dist :dist}]
    (utils/foppl-error "Sample is not a value"))

  (visit-observe [v {dist :dist val :val}]
    (utils/foppl-error "Observe is not a value")))

(defn- builtin? [name]
  (contains? eval/all-builtins name))

(defn- builtin-callable [name]
  (get eval/all-builtins name))

(defn- to-clojure-value
  ([n] (to-clojure-value n {}))

  ([n env] (let [v (clojure-value-visitor. {})]
             (accept n v))))

;; evaluation-based-inference-visitor performs evaluation-based
;; inference regardless of the inference algorithm. The parameters it
;; receives are:
;;
;; * `rho`: a map from user-defined procedure name to a tuple
;;   containing the list of variable names and the expression associated
;;   with the procedure.
;;
;; * `store`: a store for state to be kept during the inference
;;   procedure. Specific to the inference algorithm used.
;;
;; * `env`: the execution environment. Stores local variables and
;;   their values at the current point of execution.
;;
;; * `sample-fn`: a function to be called when a `sample` expression
;;   is found. It is called with two arguments: the distribution to be
;;   sampled from and the inference `store`. It must return a vector
;;   where the first element is the resulting AST node, and the second
;;   is a (potentially modified) inference store.
;;
;; * `observe-fn`: similar to `sample-fn` for the `observe`
;;   expression. It is called with three arguments: the distribution
;;   on which the observation occurs, and value observed, and the
;;   inference `store`. It must return a value in the same format as
;;   `sample-fn`.
(defrecord evaluation-based-inference-visitor [rho store env sample-fn observe-fn])

(defn- with-store [new-store {rho :rho env :env sample-fn :sample-fn observe-fn :observe-fn}]
  (evaluation-based-inference-visitor. rho new-store env sample-fn observe-fn))

(defn- with-env [new-vars {rho :rho store :store env :env sample-fn :sample-fn observe-fn :observe-fn}]
  (evaluation-based-inference-visitor. rho store (merge env new-vars) sample-fn observe-fn))

(defn- eval-coll [es {store :store :as v}]
  (let [visit-expression (fn [[es-coll current-store] e]
                           (let [[reduced-e new-store] (accept e (with-store current-store v))]
                             [(into es-coll reduced-e) new-store]))]
    (reduce visit-expression [[] store] es)))

(extend-type evaluation-based-inference-visitor
  ast/visitor

  (visit-constant [{store :store} c]
    [c store])

  (visit-variable [{store :store env :env} {name :name}]
    (when-not (contains? env name)
      (utils/foppl-error (str "Error: Undefined variable: " name)))

    [(get env name) store])

  (visit-literal-vector [{store :store :as v} {es :es}]
    (let [[es new-store] (eval-coll es v)]
      [(ast/literal-vector. es) new-store]))

  (visit-literal-map [{store :store :as v} {es :es}]
    (let [[es new-store] (eval-coll es v)]
      [(ast/literal-map. es) new-store]))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/foppl-error "Procedure definitions should not exist during evaluation-based inference"))

  (visit-lambda [{store :store} lambda]
    [lambda store])

  (visit-local-binding [v {bindings :bindings es :es}]
    (utils/foppl-error "Local bindings should have been desguared during evaluation-based inference"))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/foppl-error "loop expressions should have been desugared during evaluation-based inference"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [[reduced-predicate new-store] (accept predicate v)
          interpreter (with-store new-store v)]
      (if reduced-predicate
        (accept then interpreter)
        (accept else interpreter))))

  (visit-fn-application [{rho :rho store :store :as v} {car :name args :args}]
    (let [[reduced-args new-store] (eval-coll args v)
          constant (fn [val] (ast/constant. val))]

      (cond
        (contains? rho car) (let [[vars e] (get rho car)
                                  env-extension (zipmap vars reduced-args)]
                              (accept e (with-env env-extension v)))
        (builtin? car) [(constant (apply (builtin-callable car) (map to-clojure-value reduced-args))) store]
        :else [(constant (apply (to-clojure-value car) (map to-clojure-value reduced-args))) store])))

  (visit-sample [{store :store sample-fn :sample-fn :as v} {dist :dist}]
    (let [[reduced-dist new-store] (accept dist v)]
      (sample-fn reduced-dist new-store)))

  (visit-observe [{store :store observe-fn :observe-fn :as v} {dist :dist val :val}]
    (let [[reduced-dist store-1] (accept dist v)
          [reduced-val store-2] (accept val (with-store store-1 v))]
      (observe-fn reduced-dist reduced-val store-2))))

(defn- desugar-loops [{defs :defs e :e}]
  "Desugars `loop` constructs in HOPPL (which work differently from
  their FOPPL counterparts)."
  (let [v (loop-desugar-visitor.)
        desugar (fn [n] (accept n v))]
    (ast/program. (map desugar defs) (accept e v))))

(defn- desugar-let [{defs :defs e :e :as program}]
  "`let` expressions are just sugar in HOPPL: they get translated to
  anonymous function applications."
  (let [v (let-desugar-visitor.)
        desugar (fn [n] (accept n v))]
    (ast/program. (map desugar defs) (accept e v))))

(defn- desugar [program]
  "Desugars a HOOPL program entirely: loops are desugared into `let`
  bindings; `let` bindings with multiple bindings are desugared to
  `let` forms with a single binding; and finally `let` expressions are
  removed altogether and replaced with the application of anonymous
  functions."
  (-> program
      desugar-loops
      desugar/multiple-bindings
      desugar-let))

(defn- interpret [sample-fn observe-fn store {defs :defs e :e}]
  (let [procedure-names (map :name defs)
        procedure-args (fn [{args :args}] (map :name args))
        encode-procedure (fn [procedure] [(into [] (procedure-args procedure)) (:e procedure)])
        encoded (map encode-procedure defs)
        rho (zipmap procedure-names encoded)

        v (evaluation-based-inference-visitor. rho store {} sample-fn observe-fn)]
    (accept e v)))

(defn- likelihood-init-store []
  {:log-W 0})

(defn- likelihood-sample-fn [{dist :n} store]
  [(anglican/sample* dist) store])

(defn- likelihood-observe-fn [{dist :n} {val :n :as observed} store]
  (let [log-prob (anglican/observe* dist val)
        current-weight (:log-W store)
        new-store (assoc store :log-W (+ log-prob current-weight))]
    [observed new-store]))

(defn- likelihood-weighting-inference
  ([program] (let [gen-fn (partial interpret likelihood-sample-fn likelihood-observe-fn)]
               (likelihood-weighting-inference program (likelihood-init-store) gen-fn)))

  ([program store gen-fn] (let [[val new-store] (gen-fn store program)
                                weight (:log-W new-store)]
                            (lazy-seq (cons [val weight] (likelihood-weighting-inference program new-store gen-fn))))))

(defn perform [program]
  "Performs evaluation-based inference of a HOPPL program. First, the
  program is desugared, then it is interpreted. Inference uses
  likelihood weighting."
  (-> program
      desugar
      likelihood-weighting-inference))
