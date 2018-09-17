(ns foppl.scope
  "Validates the scope of variables used in a FOPPL program.
  Traverses the AST but never performs any mutation."
  (:require [foppl.ast :as ast :refer [accept]])
  (:require [foppl.utils :as utils]))

(def ^:private builtin-functions
  ['+
   '-
   '*
   '/
   'abs
   'first
   'rest
   'last
   'nth
   'conj
   'cons
   'vector
   'loop
   'foreach])

(def ^:private distributions
  ['normal
   'uniform-continuous
   'beta
   'bernoulli
   'flip])

(def ^:private builtins
  (set (concat builtin-functions distributions)))

(defrecord environment [parent names])

(defn- new-environment []
  (environment. nil #{}))

(defn- in-scope [{parent :parent names :names} name]
  (environment. parent (conj names name)))

(defn- nest [env names]
  (environment. env (set names)))

(defn- pop-env [env]
  {:pre [(some? (:parent env))]}

  (:parent env))

(defn- resolved? [env name]
  {:pre [(some? env) (set? (:names env))]}

  (cond
    (contains? (:names env) name) true
    (some? (:parent env)) (resolved? (:parent env) name)
    :else false))

(defrecord scope-visitor [environment])

(defn- scoped [name {env :environment}]
  (let [new-env (in-scope env name)]
    (scope-visitor. new-env)))

(defn- nest-with [names {env :environment}]
  (let [nested-env (nest env names)]
    (scope-visitor. nested-env)))

(defn- unscope [{env :environment}]
  (let [new-env (pop-env env)]
    (scope-visitor. new-env)))

(defn- accept-coll [coll v]
  (let [verify (fn [v n] (accept n v))]
    (reduce verify v coll)))

(extend-type scope-visitor
  ast/visitor

  (visit-program [_ _]
    (utils/ice "program node should be inaccessible to scope visitor"))

  (visit-constant [v c]
    v)

  (visit-variable [{env :environment :as v} {name :name}]
    (when-not (resolved? env name)
      (utils/foppl-error (str "Undefined variable: " name)))
    v)

  (visit-static-vector [v static-vector]
    (accept-coll (:es static-vector) v))

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
  (let [accept-and-scope (fn ([v n] (do
                                     (accept n v)
                                     (scoped (:name n) v)))
                           ([] initial-visitor))]
    (reduce accept-and-scope initial-visitor defs)))

(defn perform [{defs :defs e :e :as program}]
  (let [visitor (scope-visitor. (new-environment))]
    (->> visitor
         (reduce-defs defs)
         (accept e))
    program))
