(ns foppl.eval
  "Performs evaluation of FOPPL expression in a sandboxed environment.
  Allows the partial evaluation of deterministic expressions in graphical
  models in order to simplify the model and reduce the number of dependencies
  among random variables."
  (:require [clojure.string :as s]
            [anglican.runtime]
            [foppl.ast :as ast :refer [accept]]
            [foppl.formatter :as formatter]
            [foppl.primitives]
            [foppl.utils :as utils])
  (:import [foppl.ast constant fn-application]))

;; defines a map from function name -> function object for every function
;; that can potentially be applied. In practice, see `valid-fn?` definition
;; for details of when functions can actually be applied from the context
;; of a FOPPL program
(def ^:private builtins-registry
  (merge (ns-map 'clojure.core) (ns-map 'anglican.runtime) (ns-map 'foppl.primitives)))

;; do not allow the evaluation of these functions in a FOPPL context
(def ^:private forbidden-core-functions
  '#{binding eval loop map reduce filter keep keep-indexed
     remove repeatedly every? not-any? some every-pred some-fn
     comp juxt partial})

(defn- valid-fn? [f]
  {:pre [(string? f)]}

  (let [ ;; remove functions with upper case characters in the name (most
        ;; likely Java class names)
        no-java-classes (fn [f] (= (s/lower-case f) f))

        ;; remove 'earmuffed' variables (i.e., no dynamic binding)
        no-earmuffs (fn [f] (complement (re-matches #"\*.*\*" f)))

        ;; do not evaluate a set of 'forbidden' core functions
        contains-forbidden (fn [f] (contains? forbidden-core-functions (symbol f)))
        no-forbidden (comp not contains-forbidden)

        ;; combine all predicates above in a single checking function
        valid? (every-pred no-java-classes no-earmuffs no-forbidden)]

    (valid? f)))

;; this simple visitor extracts the underlying constant from AST nodes
;; of type 'constant'. Useful when performing partial evaluation, where
;; the actual value of a node needs to be retrieved.
(defrecord raw-visitor [])

(extend-type raw-visitor
  ast/visitor

  (visit-constant [_ {c :n}]
    c)

  (visit-variable [_ {name :name}]
    nil)

  (visit-literal-vector [_ _]
    nil)

  (visit-literal-map [_ _]
    nil)

  (visit-procedure [_ _]
    nil)

  (visit-lambda [_ _]
    nil)

  (visit-local-binding [_ _]
    nil)

  (visit-foreach [_ _]
    nil)

  (visit-loop [_ _]
    nil)

  (visit-if-cond [_ _]
    nil)

  (visit-fn-application [_ fn-application]
    nil)

  (visit-sample [_ _]
    nil)

  (visit-observe [_ _]
    nil)
  )

(defn- raw-constants [coll]
  (let [visitor (raw-visitor.)
        raw (fn [n] (accept n visitor))]
    (map raw coll)))

(defn- safe-apply [f args default]
  "Applies function f with given `args`. If the application results in an
  exception being thrown, `default` is returned. Useful for situations when
  it is not possible to guarantee that partially evaluating an expression
  is possible."
  (try
    (ast/constant. (apply f args))
    (catch Exception _ default)))

;; Traverses the AST and evaluates sub-expressions as possible (according to the
;; definition of the EVAL function in the book).
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

  (visit-procedure [_ procedure]
    procedure)

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
    (let [;; apart from being valid, a function definition needs to be resolvable --
          ;; i.e., exist in the builtins registry
          builtin (get builtins-registry name)
          valid? (and (valid-fn? (str name)) (fn? (var-get builtin)))

          ;; extract raw Clojure datatypes for the constant values used as arguments
          ;; to this function application
          raw-arguments (raw-constants args)

          ;; unfortunately, the evaluation rules require that `get` and `nth` only
          ;; partially evaluate if the last argument is a numerical constant.
          ;; This validates this special case
          valid-data-structure-args? (cond
                                       (or (= name 'get) (= name 'nth)) (number? (last raw-arguments))
                                       :else true)

          ;; If one of the arguments to the function cannot be represented
          ;; as a raw Clojure datatype, do not attempt to partially evaluate
          ;; this function
          valid-args? (and valid-data-structure-args? (every? (comp not nil?) raw-arguments))

          ;; if the function is resolved, it can be safely evaluated
          resolved? (and valid? builtin valid-args?)

          ;; is the function being invoked a logical operator? (only
          ;; `and` and `or` currently supported)
          logical-op? (or (= name 'and) (= name 'or))

          ;; if this logical `op` is `and` and any of the arguments is `false`,
          ;; short circuit to `false`; similarly for `or` and `true`.
          try-simplify (fn [op args e]
                         (cond
                           (= op 'and) (if (some (fn [a] (= a false)) args) (ast/constant. false) e)
                           (= op 'or) (if (some (fn [a] (= a true)) args) (ast/constant. true) e)))]

      ;; if the function is resolved, return an AST node for a constant
      ;; holding the result of the evaluation. Otherwise, leave the
      ;; expression unchanged
      (cond
        ;; if this is a resolved function application, call the
        ;; function as usual with the constant value parameters
        ;; obtained above.
        resolved? (safe-apply builtin raw-arguments fn-application)

        ;; optimization for logical operators: even if the expression
        ;; has free variables, we know that `(and true e1 e2)`
        ;; evaluates to `true` regardless of `e1`, `e2`.  A similar
        ;; rationale exists for `or`. Try to simplify these cases when
        ;; possible.
        logical-op? (try-simplify name raw-arguments fn-application)

        ;; if all else fails, returns the unmodified function
        ;; application node.
        :else fn-application)))

  (visit-sample [_ sample]
    sample)

  (visit-observe [_ observe]
    observe)
  )

;; evaluates an expression where sub-expressions may not yet be
;; values, but can be reduced to one in multiple steps (i.e., there
;; are no free variables and the functions applied are all valid).
;; Produces the resuling expression as a constant if successful.
(defrecord deep-eval-visitor [])

(defn- accept-coll [es v]
  (map (fn [n] (accept n v)) es))

(extend-type deep-eval-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v {es :es}]
    (utils/ice "literal vectors not allowed in deterministic language"))

  (visit-literal-map [v {es :es}]
    (utils/ice "literal maps not allowed in deterministic language"))

  (visit-procedure [_ _]
    (utils/ice "procedure definitions not allowed in deterministic language"))

  (visit-lambda [_ _]
    (utils/ice "lambda definitions not allowed in deterministic language"))

  (visit-local-binding [_ local-binding]
    (utils/ice "local bindings not allowed in deterministic language"))

  (visit-foreach [_ foreach]
    (utils/ice "foreach not allowed in deterministic language"))

  (visit-loop [_ loop]
    (utils/ice "loop not allowed in deterministic language"))

  (visit-if-cond [v {predicate :predicate then :then else :else :as if-cond}]
    (let [raw-predicate (accept predicate v)]
      (cond
        (= raw-predicate true) (accept then v)
        (= raw-predicate false) (accept else v)
        :else if-cond)))

  (visit-fn-application [v {name :name args :args}]
    (let [;; performs evaluation of an expression that is immediately
          ;; reducible to a value
          do-eval (fn [e] (accept e (eval-visitor.)))

          ;; deeply evaluate each of the arguments passed to the
          ;; function
          evaled-args (accept-coll args v)

          ;; construct a corresponding function application AST node
          ;; where the arguments have been reduced to a value
          resulting-fn (ast/fn-application. name evaled-args)]

      ;; evaluate the resulting expression, which should be reduced to
      ;; a value using regular evaluation
      (do-eval resulting-fn)))

  (visit-sample [_ sample]
    (utils/ice "sample not allowed in deterministic language"))

  (visit-observe [_ observe]
    (utils/ice "observe not allowed in deterministic language"))
  )

(def ^:const all-builtins
  "Set of all language builtins. Includes every function defined in clojure.core
  and anglican.runtime (plus extra definitions for martrix operations)."
  (let [fns (keys builtins-registry)
        valid-fns (map symbol (filter valid-fn? (map str fns)))]
    (set valid-fns)))

(defn peval [e]
  "Performs partial evaluation of an expression (AST node 'e'). Returns
  another AST node representing the result of the evaluated expression. Note
  that not all expressions are evaluated: only function applications are, and
  only those defined in clojure.core or anglican.runtime."
  (let [visitor (eval-visitor.)]
    (accept e visitor)))

(defn deep-eval [e]
  "Deeply evaluate an expression `e`, returning an AST node
  corresponding to the value produced by the computation."
  (let [visitor (deep-eval-visitor.)]
    (accept e visitor)))
