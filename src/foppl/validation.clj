(ns foppl.validation
  "Validates well-formedness of a FOPPL program according to the semantics of
  the language."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.formatter :as formatter]
            [foppl.eval :as eval]
            [foppl.utils :as utils]))

(defn- accept-coll [coll v]
  "Visits each node in coll with visitor v"
  (let [perform (fn [n] (accept n v))]
    (doall (map perform coll))))

;; Validates whether an AST node is a procedure definition. FOPPL is composed by a
;; finite, potentially zero, number of procedure definitions followed by an expression.
;; This visitor allows the compiler to verify that every expression preceding the last
;; one is a procedure definition.
(defrecord is-defn-visitor [])

;; Validates whether an AST node is a FOPPL expression (i.e., not a procedure definition).
;; The last expression of a FOPPL program cannot be a procedure definition, and this
;; visitor allows the compiler to check that that is the case. Additionally, procedure
;; definitions cannot be nested.
(defrecord is-e-visitor [])

(defn- defn-unexpected [n]
  (utils/foppl-error (str "Expected function definition, found: " (formatter/to-str n))))

(defn- e-unexpected [n]
  (utils/foppl-error (str "Expected FOPPL expression, found: " (formatter/to-str n))))

(extend-type is-defn-visitor
  ast/visitor

  (visit-constant [_ c]
    (defn-unexpected c))

  (visit-variable [_ var]
    (defn-unexpected var))

  (visit-literal-vector [_ literal-vector]
    (defn-unexpected literal-vector))

  (visit-literal-map [_ literal-map]
    (defn-unexpected literal-map))

  (visit-procedure [_ {name :name args :args e :e}]
    ;; Warns the user if a procedure has the same name as a FOPPL builtin
    (when (contains? eval/all-builtins name)
      (utils/warning (str "Overwriting built-in function " name)))

    ;; validates that a procedure's expression does not contain
    ;; nested procedure definitions
    (accept e (is-e-visitor.)))

  (visit-lambda [_ _]
    (utils/foppl-error "Lambdas are not part of FOPPL"))

  (visit-local-binding [_ local-binding]
    (defn-unexpected local-binding))

  (visit-foreach [_ foreach]
    (defn-unexpected foreach))

  (visit-loop [_ loops]
    (defn-unexpected loops))

  (visit-if-cond [_ if-cond]
    (defn-unexpected if-cond))

  (visit-fn-application [_ fn-application]
    (defn-unexpected fn-application))

  (visit-sample [_ sample]
    (defn-unexpected sample))

  (visit-observe [_ observe]
    (defn-unexpected observe))
  )

(extend-type is-e-visitor
  ast/visitor

  (visit-constant [_ _]
    nil)

  (visit-variable [_ _]
    nil)

  (visit-literal-vector [v {es :es}]
    (accept-coll es v))

  (visit-literal-map [v {es :es}]
    (accept-coll es v))

  (visit-procedure [_ procedure]
    (e-unexpected procedure))

  (visit-lambda [v {e :e}]
    (accept e v))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          bound (map last pairs)]

      (accept-coll bound v)
      (accept-coll es v)))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          bound (map last pairs)]

      (accept c v)
      (accept-coll bound v)
      (accept-coll es v)))

  (visit-loop [v {c :c e :e f :f es :es}]
    (accept c v)
    (accept e v)
    (accept-coll es v))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (accept predicate v)
    (accept then v)
    (accept else v))

  (visit-fn-application [v {name :name args :args}]
    (accept-coll args v))

  (visit-sample [v {dist :dist}]
    (accept dist v))

  (visit-observe [v {dist :dist val :val}]
    (accept dist v)
    (accept val v))
  )

(defn perform [{defs :defs e :e :as program}]
  "Performs semantic validation of a FOPPL program. Some of the
  rules (i.e., every S-expression preceding the last one should be
  procedure definitions) are defined in the formal grammar of FOPPL, but
  not validated during parsing in this implementation. In addition, this
  also verifies that procedure definitions cannot be nested."

  (let [is-defn-v (is-defn-visitor.)
        validate-def (fn [def] (accept def is-defn-v))
        _ (doall (map validate-def defs))

        is-e-v (is-e-visitor.)
        validate-e (accept e is-e-v)]

    program))
