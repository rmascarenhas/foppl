(ns foppl.hoppl
  (:require [foppl.ast :as ast])
  (:import [foppl.ast constant variable if-cond fn-application literal-vector
            literal-map procedure lambda local-binding]))

(defn perform [program]
  (println "Running HOPPL on program:" program))
