(ns foppl.scope
  "Validates the scope of variables used in a FOPPL program.
  Ensures that every variable used can be resolved (was previously
  bound) as well as every function application is resolved to a
  known function. Traverses the AST but never performs any mutation."
  (:require [foppl.ast :as ast :refer [accept]])
  (:require [foppl.utils :as utils]))

;; ================================================================ ;;
;;                             BUILT-INS                            ;;
;; ================================================================ ;;

(def ^:private builtin-functions
  ['+
   '-
   '*
   '/
   'abs
   'first
   'last
   'rest
   'last
   'nth
   'conj
   'cons
   'vector
   'hash-map
   'append
   'get
   'put
   'set
   'loop
   'foreach])

(def ^:private distributions
  ['normal
   'discrete
   'uniform-continuous
   'beta
   'bernoulli
   'flip])

;; built-ins provided by FOPPL: some functions inherited from the host
;; (Clojure), sample/observe, as well as a slate of distribution
;; functions
(def ^:private builtins
  (set (concat builtin-functions distributions)))

;; ================================================================ ;;
;;                          ENVIRONMENTS                            ;;
;; ================================================================ ;;

;; the environment of an expression determines whether or not variables
;; are free or bound. Environments can be nested: nesting happens when
;; performing local bind ('let' expressions)
(defrecord environment [parent names])

(defn- new-environment []
  "Creates an empty, root environment"
  (environment. nil #{}))

(defn- in-scope [{parent :parent names :names} name]
  "Adds the 'name' given to the current scope of the
  environment given."
  (environment. parent (conj names name)))

(defn- nest [env names]
  "Produces a nested environment (child of 'env') that has access
  to the given list of 'names'"
  (environment. env (set names)))

(defn- pop-env [env]
  "Opposite of 'nest' function. Returns the parent environment of
  the environment given. Calling this function on the root environment
  is an error."
  {:pre [(some? (:parent env))]}

  (:parent env))

(defn- resolved? [env name]
  "Performs name resolution. Returns whether the given 'name' is
  bound with respect to the environment given."
  {:pre [(some? env) (set? (:names env))]}

  (cond
    (contains? (:names env) name) true
    (some? (:parent env)) (resolved? (:parent env) name)
    :else false))

;; ================================================================ ;;
;;                         SCOPE VISITOR                            ;;
;; ================================================================ ;;

;; Implements the ast/visitor protocol in order to determine if every variable
;; and function application is resolved. Traverses the entire AST maintaining
;; an environment that contains all known symbols.
(defrecord scope-visitor [environment])

(defn- scoped [name {env :environment}]
  "Adds the 'name' given to the list of known symbols of the visitor.
  Useful after evaluating a function definition."
  (let [new-env (in-scope env name)]
    (scope-visitor. new-env)))

(defn- nest-with [names {env :environment}]
  "Produces a scope-visitor with a nested environment, including
  the given list of 'names' to the known symbols."
  (let [nested-env (nest env names)]
    (scope-visitor. nested-env)))

(defn- unscope [{env :environment}]
  "Produces a scope-visitor that operates under the parent environment.
  Just like 'pop-env', it is an error to call this function if the visitor
  is operating with a root environment."
  (let [new-env (pop-env env)]
    (scope-visitor. new-env)))

(defn- accept-coll [coll v]
  "Visits every node in a collection sequentially, using the resulting visitor
  from one node on the next."
  (let [verify (fn [v n] (accept n v))]
    (reduce verify v coll)))

;; important note: every visitor function *must* return a scope-visitor record.
;; The returned visitor will be used to visit subsequent nodes in the AST. This is
;; important because, as the visitor traverses the AST, new names symbols may be bound
;; and they should be taken into account when validating variables and function
;; applications.
(extend-type scope-visitor
  ast/visitor

  (visit-constant [v c]
    v)

  (visit-variable [{env :environment :as v} {name :name}]
    (when-not (resolved? env name)
      (utils/foppl-error (str "Undefined variable: " name)))
    v)

  (visit-literal-vector [v literal-vector]
    (utils/ice "literal vectors should have been desgurated during scoping"))

  (visit-literal-map [v literal-map]
    (utils/ice "literal maps should have been desgurated during scoping"))

  (visit-definition [v {name :name args :args e :e}]
    (->> v
         (nest-with args)
         (accept e)
         unscope))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)
          first-name (comp :name first)
          bound-names (map first-name pairs)]
      (->> v
           (nest-with bound-names)
           (accept-coll es)
           unscope)))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (->> v
         (accept then)
         (accept else)))

  (visit-fn-application [{env :environment :as v} {name :name args :args}]
    (let [validate-fn (fn [name, v]
                        (if (or (resolved? env name) (contains? builtins name))
                          v
                          (utils/foppl-error (str "Undefined function: " name))))]
      (->> v
           (validate-fn name)
           (accept-coll args))))

  (visit-sample [v {dist :dist}]
    (->> v
         (accept dist)))

  (visit-observe [v {dist :dist val :val}]
    (->> v
         (accept dist)
         (accept val))))

(defn- reduce-defs [defs initial-visitor]
  "Validates the scope of each definition; if it succeeds, adds the name
  of the defined function to the scope, making sure subsequent definitons
  may refer to it."
  (let [accept-and-scope (fn ([v n] (do
                                     (accept n v)
                                     (scoped (:name n) v)))
                           ([] initial-visitor))]
    (reduce accept-and-scope initial-visitor defs)))

(defn perform [{defs :defs e :e :as program}]
  "Performs scope validation on every function definition and on the
  program's expression. Returns the unmodified program. Halts execution
  if a symbol that cannot be resolved is found."
  (let [visitor (scope-visitor. (new-environment))]
    (->> visitor
         (reduce-defs defs)
         (accept e))
    program))
