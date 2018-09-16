(ns foppl.ast
  "Defines AST data structures and visitor protocol."
  (:require [clojure.edn :as edn]))

;; a FOPPL program consists of a collection of definitions and
;; an expression
(defrecord program [defs e])

;; a FOPPL constant -- always numerical
(defrecord constant [n])

;; a FOPPL variable
(defrecord variable [name])

;; a FOPPL vector consists of a collection of expressions contained
;; in square brackets: [e1 e2 ... en]
(defrecord static-vector [es])

;; a FOPPL function definition consists of a name, a collection
;; of arguments, and an expression
(defrecord definition [name args e])

;; a FOPPL local binding consists of a name and value pair, and a list
;; of target expressions where substitution is going to happen. In
;; this stage, this node allows the sugared version with multiple
;; bindings in a single 'let' form. Desugaring happens during the
;; compilation pipeline, where local bindings will only be able to
;; bind a single free variable
(defrecord local-binding [bindings es])

;; a FOPPL if expression consists of a predicate and two expressions:
;; one to be evaluated if the predicate evaluates to true; and other
;; if it evaluates to false.
(defrecord if-cond [predicate then else])

;; a FOPPL function application consists of the name of the function
;; being applied, as well as a collection of arguments passed to it.
(defrecord fn-application [name args])

;; a FOPPL sample event, being applied to a distribution object 'dist'.
(defrecord sample [dist])

;; a FOPPL conditioning operation. Consists of a distribution object
;; and a value from a random variable being observed.
(defrecord observe [dist val])

(declare to-tree)

(defn- invalid-foppl [e]
  (throw (RuntimeException. (str "Invalid FOPPL expression: " e))))

(defn- handle-constant [c]
  (constant. c))

(defn- handle-variable [name]
  (variable. (str name)))

(defn- handle-vector [v]
  (static-vector. (mapv to-tree v)))

(defn- handle-defn [context]
  {:pre [(= (count context) 3) (vector? (second context))]}

  (let [[name args e] context
        name (str name)
        args (mapv str args)
        e (to-tree e)]
    (definition. name args e)))

(defn- handle-local-binding [context]
  {:pre [(>= (count context) 2)
         (vector? (first context))
         (even? (count (first context)))]}

  (let [pairs (partition 2 (first context))
        expand (fn [[name e]] (vector (str name) (to-tree e)))
        bindings (mapcat expand pairs)
        exps (rest context)
        e (map to-tree exps)]
    (local-binding. bindings e)))

(defn- handle-if-cond [context]
  {:pre [(= (count context) 3)]}

  (let [[predicate then else] context]
    (if-cond. (to-tree predicate) (to-tree then) (to-tree else))))

(defn- handle-sample [context]
  {:pre [(= (count context) 1)]}

  (sample. (to-tree (first context))))

(defn- handle-observe [context]
  {:pre [(= (count context) 2)]}

  (let [[dist val] context]
    (observe. (to-tree dist) (to-tree val))))

(defn- handle-fn-application [name args]
(let [name (str name)
      args (map to-tree args)]
  (fn-application. name args)))

(defn- handle-list [sexp]
  {:pre [(symbol? (first sexp))]}

  (let [sym (first sexp)
        cdr (rest sexp)]
    (cond
      (= sym 'defn) (handle-defn cdr)
      (= sym 'let) (handle-local-binding cdr)
      (= sym 'if) (handle-if-cond sexp cdr)
      (= sym 'sample) (handle-sample cdr)
      (= sym 'observe) (handle-observe cdr)
      :else (handle-fn-application sym cdr))))

(defn- to-tree [sexp]
  (cond
    (number? sexp) (handle-constant sexp)
    (vector? sexp) (handle-vector sexp)
    (symbol? sexp) (handle-variable sexp)
    (list? sexp) (handle-list sexp)
    :else (invalid-foppl sexp)))

(defn- to-program [[e & defs]]
  (program. defs e))

;; (defn- to-program [trees]
;;   (do
;;     (println (count trees))
;;     (loop [t trees]
;;       (when (seq t)
;;         (println (first t))
;;         (recur (rest t))))))

;; protocol to be implemented by the different kinds of visitors that
;; validate and make changes to the AST as the FOPPL program is compiled
;; to a target language (graphical model or otherwise).
(defprotocol visitor
  (visit-program [program])
  (visit-constant [c])
  (visit-variable [var])
  (visit-definition [def])
  (visit-local-binding [binding])
  (visit-if-cond [if-cond])
  (visit-fn-application [fn-application])
  (visit-sample [sampgle])
  (visit-observe [observe]))

(defn read-source [stream]
  (let [sexps (repeatedly #(edn/read {:eof :eof} stream))]
    (->> sexps
         (take-while (partial not= :eof))
         (map to-tree)
         reverse
         to-program)))
