(ns foppl.ast
  "Defines AST data structures and visitor protocol."
  (:require [clojure.edn :as edn]))

;; a FOPPL program consists of a collection of definitions and
;; an expression
(defrecord program [defs e])

;; a FOPPL function definition consists of a name, a collection
;; of arguments, and an expression
(defrecord definition [name args e])

;; a FOPPL local binding consists of a name and value pair, and
;; a target expression where substitution is going to happen
(defrecord local-binding [name val e])

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

(defn- to-tree [src]
  src)

;; protocol to be implemented by the different kinds of visitors that
;; validate and make changes to the AST as the FOPPL program is compiled
;; to a target language (graphical model or otherwise).
(defprotocol visitor
  (visit-program [program])
  (visit-definition [def])
  (visit-local-binding [binding])
  (visit-if-cond [if-cond])
  (visit-fn-application [fn-application])
  (visit-sample [sample])
  (visit-observe [observe]))

(defn read-source [src]
  (-> src
      edn/read-string
      to-tree))
