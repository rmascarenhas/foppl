(ns foppl.eval
  "Performs evaluation of FOPPL expression in a sandboxed environment.
  Allows the partial evaluation of deterministic expressions in graphical
  models in order to simplify the model and reduce the number of dependencies
  among random variables."
  (:require [clojure.string :as s])
  (:require [anglican.runtime])
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast constant fn-application])
  (:import [foppl.formatter formatter-visitor])
  (:require [foppl.formatter :as formatter]))

;; do not allow the evaluation of these functions in a FOPPL context
(def ^:private forbidden-core-functions
  #{'binding 'eval 'loop})

(defn- valid-fn? [f]
  (let [;; remove functions with upper case characters in the name (most
        ;; likely Java class names)
        no-java-classes (fn [f] (= (s/lower-case f) f))

        ;; remove 'earmuffed' variables (i.e., no dynamic binding)
        no-earmuffs (fn [f] (complement (s/includes? f "*")))

        ;; do not evaluate a set of 'forbidden' core functions
        no-forbidden (fn [f] (complement (contains? forbidden-core-functions (symbol f))))

        ;; combine all predicates above in a single checking function
        valid? (every-pred no-java-classes no-earmuffs no-forbidden)]

    (valid? f)))

(defn- eval-str [str]
  {:pre [(string? str)]}
  "Evaluates an expression (as a string) in a sandboxed environment.
  Functions from clojure.core and anglican.runtime are available."

  (let [ ;; name of the active namespace when calling this function
        previous-ns *ns*

        ;; create a temporary namespace for evaluating the expression
        ;; given (as a string)
        eval-ns-name (gensym "foppl-eval-ns")
        eval-ns (create-ns eval-ns-name)

        ;; makes sure the temporary namespace create has access to
        ;; clojure core functions and anglican runtime functions
        _ (binding [*ns* eval-ns] (refer-clojure) (refer 'anglican.runtime))]

    (try
      (in-ns eval-ns-name)
      (eval (read-string str))
      (finally
        (in-ns (ns-name previous-ns))
        (remove-ns eval-ns-name)))))

;; the wrapping visitor makes sure that AST nodes holding constant list values
;; are wrapped to (list ...) function calls. This makes list results generated
;; by partial evaluation of expressions to be reusable in the evaluation of
;; other expressions during the compilation pipeline.
(defrecord wrap-visitor [])

(extend-type wrap-visitor
  ast/visitor

  (visit-constant [_ {c :n :as constant}]
    (if (or (list? c) (chunked-seq? c))
      (ast/fn-application. 'list (map (fn [n] (ast/constant. n)) c))
      constant))

  (visit-variable [_ var]
    var)

  (visit-literal-vector [_ literal-vector]
    literal-vector)

  (visit-literal-map [_ literal-map]
    literal-map)

  (visit-definition [_ definition]
    definition)

  (visit-local-binding [_ local-binding]
    local-binding)

  (visit-foreach [_ foreach]
    foreach)

  (visit-loop [_ loop]
    loop)

  (visit-if-cond [_ if-cond]
    if-cond)

  (visit-fn-application [_ fn-application]
    fn-application)

  (visit-sample [_ sample]
    sample)

  (visit-observe [_ observe]
    observe)
  )

(defn- wrap-coll [coll]
  (let [visitor (wrap-visitor.)
        wrap (fn [n] (accept n visitor))]
    (map wrap coll)))

(defrecord eval-visitor [])

(extend-type eval-visitor
  ast/visitor

  (visit-constant [_ {c :n :as constant}]
    (cond
      (= c true) true
      (= c false) false
      :else constant))

  (visit-variable [_ var]
    var)

  (visit-literal-vector [_ literal-vector]
    literal-vector)

  (visit-literal-map [_ literal-map]
    literal-map)

  (visit-definition [_ definition]
    definition)

  (visit-local-binding [_ local-binding]
    local-binding)

  (visit-foreach [_ foreach]
    foreach)

  (visit-loop [_ loop]
    loop)

  (visit-if-cond [v {predicate :predicate then :then else :else :as if-cond}]
    (let [raw-predicate (accept predicate v)]
      (cond
        (= raw-predicate true) then
        (= raw-predicate false) else
        :else if-cond)))

  (visit-fn-application [v {name :name args :args :as fn-application}]
    (let [valid? (valid-fn? (str name))

          ;; apart from being valid, a function definition needs to be resolvable
          ;; in the sandboxed namespace where evaluation happens.
          resolved? (and valid? (eval-str (str "(resolve '" name ")")))

          ;; wrap arguments in (list ...) function calls. This makes sure that
          ;; lists generated from previous partial evaluations can be used
          ;; to generate further results
          wrapped-args (wrap-coll args)
          wrapped-fn (ast/fn-application. name wrapped-args)

          ;; serialize the function being evaluated to a string so that
          ;; it can be evaluated by Clojure
          formatter (formatter/formatter-visitor.)
          sexp (accept wrapped-fn formatter)]

      ;; if the function is resolved, return an AST node for a constant
      ;; holding the result of the evaluation. Otherwise, leave the
      ;; expression unchanged
      (if resolved?
        (ast/constant. (eval-str sexp))
        fn-application)))

  (visit-sample [_ sample]
    sample)

  (visit-observe [_ observe]
    observe)
  )

(defn peval [e]
  "Performs partial evaluation of an expression (AST node 'e'). Returns
  another AST node representing the result of the evaluated expression. Note
  that not all expressions are evaluated: only function applications are, and
  only those defined in clojure.core or anglican.runtime."
  (let [visitor (eval-visitor.)]
    (accept e visitor)))
