(ns foppl.autodiff
  "Performs reverse-mode automatic differentiation."
  (:require [foppl.ast :as ast])
  (:import [foppl.ast definition]))

(def f1
  '(fn [x] (exp (sin x))))

;; Parses an anonymous function definition into an AST (the same used to manipulate
;; FOPPL programs).
(defn- to-tree [f]
  {:pre [(list? f)              ;; f is a list: (fn [args] e)
         (= (count f) 3)        ;; with 3 pars ('fn, [args] and e)
         (= (first f) 'fn)       ;; the first is the 'fn keyword
         (vector? (second f))]} ;; the list of arguments is a vector

  (let [args (second f)
        e (last f)]
    (ast/definition. nil args (ast/to-tree e))))

(defn- reverse-diff [n] n)

(defn diff [f]
  (-> f
      to-tree
      reverse-diff))
