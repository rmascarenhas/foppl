(ns foppl.primitives
  "A set of primitive functions that are available during partial
  evaluation of FOPPL programs."
  (:require [clojure.core.matrix :as matrix])
  (:require [anglican.runtime :refer [tanh]]))

(defn append [& args]
  (apply conj args))

(defn mat-mul [& args]
  (apply matrix/mmul args))

(defn mat-add [& args]
  (apply matrix/add args))

(defn mat-transpose [& args]
  (apply matrix/transpose args))

(defn mat-tanh [M]
  (matrix/emap tanh M))

(defn mat-relu [M]
  (matrix/emap (fn [x] (if (> x 0) x 0)) M))

(defn mat-repmat [M r c]
  (let [R (reduce (partial matrix/join-along 0) (repeat r M))]
    (reduce (partial matrix/join-along 1) (repeat c R))))
