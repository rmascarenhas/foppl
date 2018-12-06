(ns foppl.hoppl
  "This module implements evaluation-based inference. It extends FOPPL
  by adding higher-order features to it: specifically, HOPPL allows
  the use of anonymous functions and recursion."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.desugar :as desugar]
            [foppl.eval :as eval]
            [foppl.utils :as utils]
            [anglican.stat :as stat]
            [anglican.runtime :as anglican])
  (:import [foppl.ast constant variable if-cond fn-application literal-vector
            literal-map procedure lambda local-binding sample observe program]))

;; Definitions of higher-order functions supported by HOPPL.  These
;; definitions are parsed and added to the list of procedure
;; definitions available to HOPPL programs.
(def ^:private hoppl-map '(defn map [f coll]
                            (if (empty? coll)
                              (list)
                              (cons (f (first coll) (map f (rest coll)))))))

(def ^:private hoppl-reduce '(defn reduce [f x coll]
                               (if (empty? coll)
                                 x
                                 (reduce f (f x (first coll)) (rest coll)))))

(def ^:private hoppl-repeatedly '(defn repeatedly [n f]
                                   (if (<= n 0)
                                     (list)
                                     (cons (f) (repeatedly (- n 1) f)))))

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

  (visit-sample [v {dist :dist uuid :uuid}]
    (ast/sample. (accept dist v) uuid))

  (visit-observe [v {dist :dist val :val uuid :uuid}]
    (ast/observe. (accept dist v) (accept val v) uuid)))

(defrecord clojure-value-visitor [])

(extend-type clojure-value-visitor
  ast/visitor

  (visit-constant [_ {n :n}]
    n)

  (visit-variable [_ {name :name}]
    (utils/ice "Expression should be closed"))

  (visit-literal-vector [v {es :es}]
    (into [] (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (let [elements (accept-coll es v)
          to-vec (fn [coll] (into [] coll))
          partitions (map to-vec (partition 2 elements))
          map-elements (to-vec partitions)]
      (into {} map-elements)))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/ice "Procedure definitions should not exist when computing Clojure value"))

  (visit-lambda [{env :env :as v} {name :name args :args e :e}]
    (utils/ice "Lambdas should have been evaluated when compuign Clojure value"))

  (visit-local-binding [v {bindings :bindings es :es}]
    (utils/ice "Local bindings should have been removed when computing Clojure value"))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/ice "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/ice "loop expressions should have been desugared"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (utils/ice "If conditions should have been removed when computing Clojure value"))

  (visit-fn-application [v {name :name args :args}]
    (utils/ice "Function application is not a value"))

  (visit-sample [v {dist :dist}]
    (utils/ice "Sample is not a value"))

  (visit-observe [v {dist :dist val :val}]
    (utils/ice "Observe is not a value")))

(defn- builtin? [name]
  "Tests whether or not a function of the given `name` is a HOPPL
  builtin. The list of builtins available is given in
  `eval/all-builtins`."
  (contains? eval/all-builtins name))

(defn- to-clojure-value  [n]
  "Transforms an AST node `n` in its corresponding Clojure value."
  (let [v (clojure-value-visitor.)]
    (accept n v)))

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
;;   is found. It is called with three arguments: the distribution to
;;   be sampled from, the inference `store`, and the UUID associated
;;   with the `sample` AST node. It must return a vector where the
;;   first element is the resulting AST node, and the second is a
;;   (potentially modified) inference store.
;;
;; * `observe-fn`: similar to `sample-fn` for the `observe`
;;   expression. It is called with four arguments: the distribution on
;;   which the observation occurs, the value observed, the inference
;;   `store`, and the uuid of the `observe` AST node. It must return a
;;   value in the same format as `sample-fn`.
(defrecord evaluation-based-inference-visitor [rho store env sample-fn observe-fn])

(defn- with-store [new-store {rho :rho env :env sample-fn :sample-fn observe-fn :observe-fn}]
  "Returns an evaluation-based visitor where the store is the one
  given as the first parameter `new-store`. All other parameters
  remain unchanged."
  (evaluation-based-inference-visitor. rho new-store env sample-fn observe-fn))

(defn- with-env [new-vars {rho :rho store :store env :env sample-fn :sample-fn observe-fn :observe-fn}]
  "Extends the execution environment with `new-vars`, a map from
  variable name to values (constant AST nodes)."
  (evaluation-based-inference-visitor. rho store (merge env new-vars) sample-fn observe-fn))

(defn- eval-coll [es {store :store :as v}]
  "Evaluates a collection of expressions, accumulating changes to the
  inference `store` as expressions are evaluated. Returns a two
  element array where the first element is the collection of reduced
  expressions, and the second element is the resulting inference
  store."
  (let [visit-expression (fn [[es-coll current-store] e]
                           (let [[reduced-e new-store] (accept e (with-store current-store v))]
                             [(conj es-coll reduced-e) new-store]))]
    (reduce visit-expression [[] store] es)))

(extend-type evaluation-based-inference-visitor
  ast/visitor

  (visit-constant [{store :store} c]
    [c store])

  (visit-variable [{store :store env :env} {name :name}]
    ;; only variables contained in the evaluation environment are
    ;; defined.  Referencing any other variable is an error indicating
    ;; that the user attempted to use an undefined/unbound variable.
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
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [;; find the name of the variable being bound, as well as the
          ;; value.
          bound-name (:name (first bindings))
          bound-val (second bindings)

          ;; reduce the bound value
          [c1 new-store] (accept bound-val v)

          ;; extend the environment to bind the name to the reduced
          ;; value
          env-extension {bound-name c1}
          e (first es)

          ;; the expression in which the new name is bound is then
          ;; reduced by a visitor with the new store and with its
          ;; evaluation environment extended to include the variable
          ;; binding being introduced.
          visitor (->> v
                       (with-env env-extension)
                       (with-store new-store))]
      (accept e (with-env env-extension visitor))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/foppl-error "loop expressions should have been desugared during evaluation-based inference"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [[reduced-predicate new-store] (accept predicate v)
          interpreter (with-store new-store v)]
      (if (to-clojure-value reduced-predicate)
        (accept then interpreter)
        (accept else interpreter))))

  (visit-fn-application [{rho :rho env :env store :store :as v} {name :name args :args}]
    (let [[reduced-args new-store] (eval-coll args v)
          clojure-args (map to-clojure-value reduced-args)]

      (cond
        ;; if the function being applied is a user-defined procedure
        ;; (or a builtin higher order function), we extend the
        ;; environment with the function parameters being bound to the
        ;; arguments passed, and recursively evaluate the expression
        ;; contained in the procedure definition
        (contains? rho name) (let [[param-names e] (get rho name)
                                   env-extension (zipmap param-names reduced-args)
                                   visitor (->> v
                                                (with-store new-store)
                                                (with-env env-extension))]

                               (accept e visitor))

        ;; in case the function being applied is a built-in,
        ;; first-order function, we immediately apply it with the
        ;; arguments given. The result should be a constant value.
        (builtin? name) [(ast/constant. (apply (eval/builtin-fn name) clojure-args)) store]

        ;; if the function being applied is in the evaluation context,
        ;; it means it was defined as a lambda previously (no
        ;; type-checking to ensure this is actually the case is
        ;; performed).
        ;;
        ;; This case is similar to the user-defined procedure
        ;; scenario. The value associated with the name in the
        ;; evaluation environment is treated as a lambda AST node, the
        ;; environment is extended with the lambda parameters being
        ;; bound to the arguments passed, and the expression
        ;; associated with the lambda is recursively evaluated.
        (contains? env name) (let [{name :name params :args e :e} (get env name)
                                   params-names (map :name params)
                                   env-extension (zipmap params-names reduced-args)]
                               (accept e (with-env env-extension v)))

        :else (utils/foppl-error (str "Undefined function: " name)))))

  (visit-sample [{store :store sample-fn :sample-fn :as v} {dist :dist uuid :uuid}]
    ;; behavior is inference-algorithm specific. Invoke the
    ;; `sample-fn` function passed to the visitor.
    (let [[reduced-dist new-store] (accept dist v)]
      (sample-fn reduced-dist new-store uuid)))

  (visit-observe [{store :store observe-fn :observe-fn :as v} {dist :dist val :val uuid :uuid}]
    ;; behavior is inference-algorithm specific. Invoke the
    ;; `observe-fn` function passed to the visitor.
    (let [[reduced-dist store-1] (accept dist v)
          [reduced-val store-2] (accept val (with-store store-1 v))]
      (observe-fn reduced-dist reduced-val store-2 uuid))))

(defn- desugar-loops [{defs :defs e :e}]
  "Desugars `loop` constructs in HOPPL (which work differently from
  their FOPPL counterparts)."
  (let [v (loop-desugar-visitor.)
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
      desugar/multiple-bindings))

(defn- ho-builtins [{defs :defs e :e}]
  "Includes higher-order builtin definitions to the map of
  'user-defined' procedures. Returns the resulting program."
  (ast/program. (concat defs (map ast/to-tree [hoppl-map hoppl-reduce hoppl-repeatedly])) e))

(defn- interpret [sample-fn observe-fn store {defs :defs e :e}]
  "Inference-algorithm agnostic evaluation-based function. `sample-fn`
  and `observe-fn` are called whenever a `sample` or `observe`
  expressions are found, respectively. See definiton of
  `evaluation-based-inference-visitor` for information on their
  expected signatures."
  (let [;; procedure names of user-defined functions and higher-order
        ;; builtins
        procedure-names (map :name defs)
        procedure-args (fn [{args :args}] (map :name args))
        encode-procedure (fn [procedure] [(into [] (procedure-args procedure)) (:e procedure)])
        encoded (map encode-procedure defs)

        ;; the rho map is a map from procedure name to a tuple
        ;; (vector) containing [list-of-variable-names expression]
        rho (zipmap procedure-names encoded)

        v (evaluation-based-inference-visitor. rho store {} sample-fn observe-fn)]
    (accept e v)))

(defn- likelihood-init-store []
  "Initializes the store for a likelihood-weight based inference
  algorithm."
  {:log-W 0})

(defn- likelihood-sample-fn [{dist :n} store _]
  "Function to be invoked on every `sample` expression in a
  likelihood-weighting based inference algorithm. The distribution is
  sampled with Anglican, and the store is unmodified."
  [(ast/constant. (anglican/sample* dist)) store])

(defn- likelihood-observe-fn [{dist :n} {val :n :as observed} store _]
  "Function to be invoked on every `observe` expression in a
  likelihood-weighting based inference algorithm. The log-likelihood
  of the observation in the distribution given is calculated, and
  added to the store. The modified store is then returned."
  (let [log-prob (anglican/observe* dist val)
        current-weight (:log-W store)
        new-store (assoc store :log-W (+ log-prob current-weight))]
    [observed new-store]))

(defn- perform-inference
  "Performs evaluation-based inference. Inference algorithm is dicated
  by the `init-store`, `sample-fn` and `obseve-fn` parameters passed."

  ;; given a program, derive a generator function to be used in the
  ;; construction of a lazy sequence of samples.
  ([program init-store sample-fn observe-fn]
   (let [gen-fn (partial interpret sample-fn observe-fn)]
     (perform-inference program (init-store) gen-fn)))

  ;; builds a lazy sequence of weighted samples by running the
  ;; model. Each element in the lazy sequence is in the format `[value
  ;; weight]`.
  ([program store gen-fn] (let [retry-on-exception #(let [result (try (gen-fn store program)
                                                                      (catch java.lang.StackOverflowError _
                                                                        :stack-overflow))]
                                                      ;; Retry in case running the model causes a stack overflow.
                                                      (if (= result :stack-overflow)
                                                        (do
                                                          (println "Stack overflow. Trying again.")
                                                          (recur))
                                                        result))
                                [val new-store] (retry-on-exception)
                                weight (:log-W new-store)]
                            (lazy-seq (cons [val weight] (perform-inference program store gen-fn))))))

(defn forward [program init-store sample-fn observe-fn]
  "Runs the generative model forward once."

  (->> program
       desugar
       ho-builtins
       (interpret sample-fn observe-fn (init-store))))

(defn perform
  "Performs evaluation-based inference of a HOPPL program. First, the
  program is desugared, then it is interpreted. If only the program is
  passed, likelihood-weighting inference is performed."

  ([program] (perform program likelihood-init-store likelihood-sample-fn likelihood-observe-fn))

  ([program init-store sample-fn observe-fn]
   (-> program
       desugar
       ho-builtins
       (perform-inference init-store sample-fn observe-fn))))

(defn empirical-mean [samples]
  "Calculates the empirical mean given a collection of samples (in the
  format returned by the `perform` function)."
  (let [;; aggregate the sampled values
        values (map (comp :n first) samples)

        ;; and their weights
        weights (map second samples)

        ;; if there was no observation in the model, the
        ;; log-probability of every sample is going to be zero
        unobserved? (every? zero? weights)

        ;; to calculate the mean, we use `mean` if there were no
        ;; observations, or Anglican's `empirical-mean` if there were.
        mean-fn (if unobserved? (comp float anglican/mean) stat/empirical-mean)

        ;; Due to the difference in mean-calculating functions above,
        ;; we need to format the results differently based on whether
        ;; or not there were any observations in the model. In
        ;; particular, `empirical-mean` expects a map of
        ;; log-probablity -> value.
        collect-results #(if unobserved? %1 (zipmap %1 %2))]
    (-> values
        (collect-results weights)
        mean-fn)))
