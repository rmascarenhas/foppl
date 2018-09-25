(ns foppl.eval
  "Performs evaluation of FOPPL expression in a sandboxed environment.
  Allows the partial evaluation of deterministic expressions in graphical
  models in order to simplify the model and reduce the number of dependencies
  among random variables."
  (:require [clojure.string :as s])
  (:require [anglican.runtime])
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast constant fn-application])
  (:require [foppl.formatter :as formatter])
  (:import [foppl.formatter formatter-visitor])
  (:require [foppl.utils :as utils]))

;; defines a map from function name -> function object for every function
;; that can potentially be applied. In practice, see `valid-fn?` definition
;; for details of when functions can actually be applied from the context
;; of a FOPPL program
(def ^:private builtins-registry
  (merge (ns-map 'clojure.core) (ns-map 'anglican.runtime)))

;; do not allow the evaluation of these functions in a FOPPL context
(def ^:private forbidden-core-functions
  #{'binding 'eval 'loop})

(defn- valid-fn? [f]
  {:pre [(string? f)]}

  (let [ ;; remove functions with upper case characters in the name (most
        ;; likely Java class names)
        no-java-classes (fn [f] (= (s/lower-case f) f))

        ;; remove 'earmuffed' variables (i.e., no dynamic binding)
        no-earmuffs (fn [f] (complement (s/includes? f "*")))

        ;; do not evaluate a set of 'forbidden' core functions
        no-forbidden (fn [f] (complement (contains? forbidden-core-functions (symbol f))))

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

  (visit-variable [_ _]
    (utils/ice "Variables have no raw value"))

  (visit-literal-vector [_ _]
    (utils/ice "Literal vectors have no raw value"))

  (visit-literal-map [_ _]
    (utils/ice "Literal maps have no raw value"))

  (visit-definition [_ _]
    (utils/ice "Definitions have no raw value"))

  (visit-local-binding [_ _]
    (utils/ice "Local bindings have no raw value"))

  (visit-foreach [_ _]
    (utils/ice "foreach have no raw values"))

  (visit-loop [_ _]
    (utils/ice "Loops have no raw value"))

  (visit-if-cond [_ _]
    (utils/ice "if expressions have no raw values"))

  (visit-fn-application [_ _]
    (utils/ice "function applications have no raw values"))

  (visit-sample [_ _]
    (utils/ice "Samples have no raw values"))

  (visit-observe [_ _]
    (utils/ice "Observations have no raw values"))
  )

(defn- raw-constants [coll]
  (let [visitor (raw-visitor.)
        raw(fn [n] (accept n visitor))]
    (map raw coll)))

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

          ;; apart from being valid, a function definition needs to be resolvable --
          ;; i.e., exist in the builtins registry
          builtin (get builtins-registry name)
          resolved? (and valid? builtin)]

      ;; if the function is resolved, return an AST node for a constant
      ;; holding the result of the evaluation. Otherwise, leave the
      ;; expression unchanged
      (if resolved?
        (ast/constant. (apply builtin (raw-constants args)))
        fn-application)))

  (visit-sample [_ sample]
    sample)

  (visit-observe [_ observe]
    observe)
  )

(def ^:const all-functions
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
