(ns foppl.ast
  "Defines AST data structures and visitor protocol."
  (:require [foppl.utils :as utils]
            [clojure.set :as set]
            [clojure.edn :as edn])

  (:import [java.util UUID]))

;; ================================================================ ;;
;;                          RECORD DEFINITIONS                      ;;
;; ================================================================ ;;

;; a FOPPL program consists of a collection of definitions and
;; an expression
(defrecord program [defs e])

;; a FOPPL constant -- could be numerical, string, boolean, a distrbution, etc.
(defrecord constant [n])

;; a FOPPL variable
(defrecord variable [name])

;; a FOPPL vector consists of a collection of expressions contained
;; in square brackets: [e1 e2 ... en]. Desugared during the compilation
;; process to an application of the 'vector' builtin.
(defrecord literal-vector [es])

;; a FOPPL map consists of an even number of expressions surrounded by
;; curly braces: {e1 e'1 e2 e'2 ... en e'n}. Desugared during the
;; compilation process to an application of the 'hash-map' builtin
(defrecord literal-map [es])

;; a FOPPL procedure definition consists of a name, a collection
;; of arguments, and an expression
(defrecord procedure [name args e])

;; a lambda expression is not part of the FOPPL grammar. It can only
;; be directly created by the compiler (i.e., when performing
;; automatic differentiation in some sampling procedure). In the
;; context of the HOPPL, lambdas can appear anywhere an expression is
;; accepted.
(defrecord lambda [name args e])

;; a thunk is a piece of deferred execution. Every thunk node has a
;; unique identifier, a type and the arguments to realize the
;; thunk. Thunks are only used during lazy-evaluation of a model with
;; a separate inference engine.
(defrecord thunk [id type args])

;; a FOPPL local binding consists of a name and value pair, and a list
;; of target expressions where substitution is going to happen. In
;; this stage, this node allows the sugared version with multiple
;; bindings in a single 'let' form. Desugaring happens during the
;; compilation pipeline, where local bindings will only be able to
;; bind a single free variable
(defrecord local-binding [bindings es])

;; a FOPPL foreach construct is sugared syntax that easily allows a set of
;; expressions to be evaluated across many collections. Every name in the
;; collection of bindings given needs to bind to a collection of the
;; same length. This is desugared to a sequence of local bindings mapped
;; to a vector
(defrecord foreach [c bindings es])

;; a FOPPL loop construct is another sugared syntax that enables computations
;; to be stitched together. The function f is applied to each element of
;; the collection, and the result of the computation is passed along as a
;; parameter to the next computation.
(defrecord loops [c e f es])

;; a FOPPL if expression consists of a predicate and two expressions:
;; one to be evaluated if the predicate evaluates to true; and other
;; if it evaluates to false.
(defrecord if-cond [predicate then else])

;; a FOPPL function application consists of the name of the function
;; being applied, as well as a collection of arguments passed to it.
(defrecord fn-application [name args])

;; a FOPPL sample event, being applied to a distribution object 'dist'.
(defrecord sample [dist uuid])

;; a FOPPL conditioning operation. Consists of a distribution object
;; and a value from a random variable being observed.
(defrecord observe [dist val uuid])

(defn- new-uuid []
  "Utility method. Generates a unique, random UUID for sample and
  observe statements. Can later be used to provide a unique address to
  random variables that is going to remain the same after multiple
  executions of a previously parsed program."

  (str (UUID/randomUUID)))

;; ================================================================ ;;
;;                         TRAVERSAL FUNCTIONS                      ;;
;; ================================================================ ;;

;; indicate to the Clojure compiler that we have a 'to-tree' symbol. Traversal
;; of the FOPPL code/data-structure happens via indirect recursion
(declare to-tree)

(defn- invalid-foppl [e]
  "This function throws a RuntimeException indicating that the expression
  given is invalid. Should only be calle when an expression is not recognized."
  (throw (RuntimeException. (str "Invalid FOPPL expression: " e))))

(defn- handle-constant [c]
  "Creates a (numerical) constant record."
  (constant. c))

(defn- handle-variable [name]
  "Creates a variable record that tags the name given as a variable."
  (variable. (symbol name)))

(defn- handle-vector [v]
  "Vectors declared with square braces [e1 e2 ... en]"
  (literal-vector. (mapv to-tree v)))

(defn- handle-map [m]
  (let [tree-map (zipmap (map to-tree (keys m)) (map to-tree (vals m)))]
    (literal-map. (flatten (into [] tree-map)))))

(defn- handle-procedure [context]
  {:pre [(= (count context) 3) (vector? (second context))]}
  "Creates a function definition node: (defn name [a1 a2 ... an] e)"

  (let [[name args e] context
        name (symbol name)
        args (mapv to-tree args)
        e (to-tree e)]
    (procedure. name args e)))

(defn- handle-lambda [context]
  {:pre [(or (and (= (count context) 2) (vector? (first context))) (and (= (count context) 3) (vector? (second context))))]}
  "Creates an anonymous function definition. Not part of the FOPPL
  language, but used to parse expressions generated by the compiler at
  different stages during compilation/inference.

  Lambdas are also part of the definiton of the HOPPL language, which
  accepts functions as values."

  (let [;; an anonymous function could or could not have an associated
        ;; name.  In case no name was given, create a lambda AST node
        ;; with `nil` name.
        normalized-context (if (= (count context) 3) context [nil (first context) (second context)])
        [name args e] normalized-context
        args (mapv to-tree args)
        e (to-tree e)]
    (lambda. name args e)))

(defn- handle-local-binding [context]
  {:pre [(>= (count context) 2)
         (vector? (first context))
         (even? (count (first context)))
         (> (count (first context)) 0)
         (every? symbol? (map first (partition 2 (first context))))]}
  "Introduces local binding: (let [name val name2 val2] e1 e2 ... en)"

  (let [pairs (partition 2 (first context))
        expand (fn [[name e]] (vector (to-tree name) (to-tree e)))
        bindings (mapcat expand pairs)
        exps (rest context)
        es (map to-tree exps)]
    (local-binding. bindings es)))

(defn- handle-foreach [context]
  {:pre [(>= (count context) 2) ;; context: constant c, bindings and expressions
         (number? (first context)) ;; number of iterations needs to be a constant
         (vector? (second context)) ;; bindings are given in a vector form
         (even? (count (second context)))]} ;; there needs to be an even number of elements in the bindings
  "Sugared language construct to allow easy iteration over collections"

  (let [c (first context)
        bindings (second context)
        es (rest (rest context))]
    (foreach. (to-tree c) (map to-tree bindings) (map to-tree es))))

(defn- handle-loop [context]
  {:pre [(>= (count context) 4)      ;; context: constant c, initial expression e, function f, and arguments
         (number? (first context))   ;; number of iterations needs to be a constant (TODO: this is not the case for HOPPL)
         (symbol? (nth context 2))]} ;; function name needs to be a symbol
  "Sugared language construct to allow cumulative computations"

  (let [c (first context)
        e (second context)
        f (nth context 2)
        es (rest (rest (rest context)))]
    (loops. (to-tree c) (to-tree e) f (map to-tree es))))

(defn- handle-if-cond [context]
  {:pre [(or (= (count context) 2) (= (count context) 3))]}
  "If expressions: (if predicate e1 e2)"

  (let [[predicate then else] context

        ;; `if` expressions may or may not have an `else` expression
        ;; as part of their definition. Lack of that clause is
        ;; equivalent to having the `nil` constant in its place.
        else (if else (to-tree else) (constant. nil))]

    (if-cond. (to-tree predicate) (to-tree then) else)))

(defn- handle-sample [context]
  {:pre [(= (count context) 1)]}
  "Sampling from a distribution object."

  (sample. (to-tree (first context)) (new-uuid)))

(defn- handle-observe [context]
  {:pre [(= (count context) 2)]}
  "Conditioning: observing a certain value on a distribution object.
  (observe dist val)"

  (let [[dist val] context]
    (observe. (to-tree dist) (to-tree val) (new-uuid))))

(defn- handle-fn-application [name args]
  "Function application. Function must be previously declared using
  'defn' or be a built-in function."
  (let [name (symbol name)
        args (map to-tree args)]
    (fn-application. name args)))

(defn- handle-list [sexp]
  {:pre [(symbol? (first sexp))]}
  "Recursively traverses a list, parsing each element."

  (let [sym (first sexp)
        cdr (rest sexp)]
    (cond
      (= sym 'defn) (handle-procedure cdr)
      (= sym 'fn) (handle-lambda cdr)
      (= sym 'let) (handle-local-binding cdr)
      (= sym 'foreach) (handle-foreach cdr)
      (= sym 'loop) (handle-loop cdr)
      (= sym 'if) (handle-if-cond cdr)
      (= sym 'sample) (handle-sample cdr)
      (= sym 'observe) (handle-observe cdr)
      :else (handle-fn-application sym cdr))))

(defn- to-program [[e & defs]]
  "Creates a program record for the FOPPL program that consists of the
  expression 'e' given and the collection of definitions 'def'"
  (program. defs e))

;; ================================================================ ;;
;;                             PROTOCOLS                            ;;
;; ================================================================ ;;

;; protocol to be implemented by the different kinds of visitors that
;; validate and make changes to the AST as the FOPPL program is compiled
;; to a target language (graphical model or otherwise).
(defprotocol visitor
  (visit-constant [v c])
  (visit-variable [v var])
  (visit-literal-vector [v literal-vector])
  (visit-literal-map [v literal-map])
  (visit-procedure [v def])
  (visit-lambda [v lam])
  (visit-thunk [v thunk])
  (visit-local-binding [v binding])
  (visit-foreach [v foreach])
  (visit-loop [v loops])
  (visit-if-cond [v if-cond])
  (visit-fn-application [v fn-application])
  (visit-sample [v sample])
  (visit-observe [v observe]))

(defprotocol node
  (accept [n v]))

(extend-type constant
  node
  (accept [n v]
    (visit-constant v n)))

(extend-type variable
  node
  (accept [n v]
    (visit-variable v n)))

(extend-type literal-vector
  node
  (accept [n v]
    (visit-literal-vector v n)))

(extend-type literal-map
  node
  (accept [n v]
    (visit-literal-map v n)))

(extend-type procedure
  node
  (accept [n v]
    (visit-procedure v n)))

(extend-type lambda
  node
  (accept [n v]
    (visit-lambda v n)))

(extend-type thunk
  node
  (accept [n v]
    (visit-thunk v n)))

(extend-type local-binding
  node
  (accept [n v]
    (visit-local-binding v n)))

(extend-type foreach
  node
  (accept [n v]
    (visit-foreach v n)))

(extend-type loops
  node
  (accept [n v]
    (visit-loop v n)))

(extend-type if-cond
  node
  (accept [n v]
    (visit-if-cond v n)))

(extend-type fn-application
  node
  (accept [n v]
    (visit-fn-application v n)))

(extend-type sample
  node
  (accept [n v]
    (visit-sample v n)))

(extend-type observe
  node
  (accept [n v]
    (visit-observe v n)))

(defn- accept-coll [coll v]
  "Given a collection of AST nodes and a node visitor, this function will apply
  the visitor to all elements of the collection."
  (let [perform (fn [n] (accept n v))]
    (doall (map perform coll))))

;; an AST visitor that performs substitution of a variable of the given
;; name for expression 'e' in some target expression
(defrecord substitution-visitor [name e])

(extend-type substitution-visitor
  visitor

  (visit-literal-vector [v {es :es}]
    (literal-vector. (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (literal-map. (accept-coll es v)))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during substitution"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during substitution"))

  (visit-constant [_ c]
    c)

  (visit-variable [{name :name e :e} {var-name :name :as var}]
    (if (= name var-name) e var))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/foppl-error "function definitions should not be inside variable substitution"))

  (visit-lambda [v {name :name args :args e :e}]
    (lambda. name args (accept e v)))

  (visit-local-binding [{name :name :as v} {bindings :bindings es :es :as local-binding}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-var (first bindings)
          bound-name (:name bound-var)
          bound-val (last bindings)
          new-bindings [bound-var (accept bound-val v)]
          es (if (= name bound-name) es (accept-coll es v))]
      (local-binding. new-bindings es)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist uuid :uuid}]
    (sample. (accept dist v) uuid))

  (visit-observe [v {dist :dist val :val uuid :uuid}]
    (observe. (accept dist v) (accept val v) uuid))
  )

;; This visitor is responsible for finding out all the free variables
;; in an expression, given a set of variables known to be bound.
(defrecord fv-visitor [bound])

;; traverses the AST starting at expressio 'e' adding 'name'
;; to the list of variables known to be bound.
(defn- accept-with-bound-name [name e {bound :bound}]
  (let [visitor (fv-visitor. (set/union bound #{name}))]
    (accept e visitor)))

(extend-type fv-visitor
  visitor

  (visit-literal-vector [_ _]
    (utils/ice "literal vectors should have been desugared during free-variable visit"))

  (visit-literal-map [_ _]
    (utils/ice "literal maps should have been desugared during free-variable visit"))

  (visit-foreach [_ _]
    (utils/ice "foreach constructs should have been desugared during free-variable visit"))

  (visit-loop [_ _]
    (utils/ice "loop constructs should have been desugared during free-variable visit"))

  (visit-constant [v {c :n}]
    (cond
      ;; if the constant holds a collection of elements, recursively traverse
      ;; each element of the collection treating each of them as a constant element
      (coll? c) (apply set/union (map (fn [el] (accept (constant. el) v)) c))

      ;; if the constant is a symbol (name of an random variable generated
      ;; by previous partial evaluation, add that to the set of free variables.
      (symbol? c) #{c}
      :else #{}))

  (visit-variable [{bound :bound} {name :name}]
    (if (contains? bound name)
      #{}
      #{name}))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/foppl-error "function definitions should not be in FOPPL expressions"))

  (visit-lambda [v {name :name args :args e :e}]
    (accept e v))

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [bound-var (first bindings)
          bound-name (:name bound-var)
          bound-val (last bindings)
          e (first es)]
      (set/union (accept bound-val v) (accept-with-bound-name bound-name e v))))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (set/union (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {args :args}]
    (apply set/union (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (accept dist v))

  (visit-observe [v {dist :dist val :val}]
    (set/union (accept dist v) (accept val v))))

;; ================================================================ ;;
;;                       PUBLIC FUNCTIONS                           ;;
;; ================================================================ ;;

(defn to-tree [sexp]
  "Given an S-expression, this function will identify the type of the expression,
  and parse deeply nested expressions recursively"
  (let [boolean? (fn [b] (or (= b false) (= b true)))]
    (cond
      (number? sexp) (handle-constant sexp)
      (string? sexp) (handle-constant sexp)
      (boolean? sexp) (handle-constant sexp)
      (vector? sexp) (handle-vector sexp)
      (map? sexp) (handle-map sexp)
      (symbol? sexp) (handle-variable sexp)
      (list? sexp) (handle-list sexp)
      :else (invalid-foppl sexp))))

(defn substitute [name e target]
  "Substitutes 'name' for expression 'e' in expression 'target'.
  Returns a modified AST subtree."
  (let [visitor (substitution-visitor. name e)]
    (accept target visitor)))

(defn free-vars [e]
  "Returns a set of free variables contained in expression 'e'"
  (let [visitor (fv-visitor. #{})]
    (accept e visitor)))

(defn fresh-sym
  "Returns an unused symbol that can be used during the compilation pipeline to stand
  for unnamed identifiers. Can optionally take a prefix."
  ([] (fresh-sym "tmp"))
  ([prefix] (gensym (str prefix "-"))))

(defn read-source [stream]
  "Reads a stream of FOPPL source code (needs to implement java.io.PushbackReader).
  Parses every expression and returns an AST representation of the source code.
  Throws an exception if there are syntax errors or an expression is not recognized."
  (let [sexps (repeatedly #(edn/read {:eof :eof} stream))]
    (->> sexps
         (take-while (partial not= :eof))
         (map to-tree)
         reverse
         to-program)))
