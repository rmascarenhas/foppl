(ns foppl.operations
  "Provides functions that manipulate the result of the compilation of a
  FOPPL program into an internal representation of a graphical model."
  (:require [clojure.set :as set]
            [anglican.runtime :as anglican]
            [foppl.formatter :as formatter]
            [foppl.ast :as ast :refer [accept]]
            [foppl.eval :as eval]
            [clojure.string :as s])
  (:import [foppl.ast constant]))

(defn count-vertices [{graph :G}]
  "Returns the number of vertices in the graphical model given."
  (count (:V graph)))

(defn count-edges [{graph :G}]
  "Returns the number of edges in the graphical model given."
  (count (:A graph)))

(defn sample-from-prior [{{P :P} :G}]
  "Produces a map of samples from prior distributions of each random
  variable defined in the graphical model given."
  (let [;; build a map from random-variable name to the AST node
        ;; representing their distribution
        extract-dist (fn [n] (first (:args n)))
        distributions (reduce (fn [m [k v]] (assoc m k (extract-dist v))) {} P)

        ;; helper function: given a map `m` and a collection of keys
        ;; `ks`, this function will produce a map containing only the
        ;; keys in `km`.
        slice (fn [m ks] (reduce (fn [m' k] (assoc m' k (get m k))) {} ks))

        ;; performs sampling of a given random variable, identified by
        ;; `name`, that behaves according to the `dist`
        ;; distribution. `samples` is a map that contains the sampling
        ;; results obtained so far from sampling previous random
        ;; variables in the collection `coll` being iterated over.
        do-sample (fn run-iter [[samples coll] [name dist]]
                    (let [;; the set of free variables contained in the distribution
                          ;; correspond to the variables that need to be sampled before
                          ;; the one we are trying to sample right now
                          fv (ast/free-vars dist)

                          ;; however, some of them may have already been sampled -- in that
                          ;; case, the sampled values should be in the `samples` map.
                          not-sampled-vars (set/difference fv (set (keys samples)))

                          ;; Recursively sample the random variables in we need that
                          ;; have not been sampled yet.
                          [new-samples _] (reduce run-iter [samples coll] (slice coll not-sampled-vars))

                          ;; substitute the value of the sampled random-variables contained in
                          ;; the `new-samples` map into the distribution expression
                          dist-e (reduce (fn [e [name val]] (ast/substitute name (ast/constant. val) e)) dist new-samples)
                          dist (:n (eval/deep-eval dist-e))

                          ;; sample from the expression obtained
                          sampled (anglican/sample* dist)

                          ;; sample from the resulting expression
                          updated-samples (assoc new-samples name sampled)]

                      ;; return the updated map of samples and the original collection
                      [updated-samples coll]))]

    ;; the reduction step according to the `do-sample` function above
    ;; will return a map of samples and the original collection -- we
    ;; are only interested in the map of samples.
    (first (reduce do-sample [{} distributions] distributions))))

(defn print-graph [{graph :G e :E :as model}]
  "Prints a representation of a graphical model to standard output."
  (let [ ;; format the PDFs for each random variable, as well as the observed
        ;; values into a textual representation for ease of understanding
        format-map (fn [m] (into {} (map (fn [[random-v e]] [random-v (symbol (formatter/to-str e))]) m)))
        formatted-pdfs (format-map (:P graph))
        formatted-observations (format-map (:Y graph))

        formatted-edges (map (fn [[from, to]] (str from "->" to)) (:A graph))

        ;; format the program's final deterministic expression too
        final-e (formatter/to-str e)]

    (println (str "Vertices: " (count-vertices model) ", Edges: " (count-edges model)))
    (println (str "V: " (:V graph)))
    (println (str "A: " (if (empty? formatted-edges) "#{}" (s/join ", " formatted-edges))))
    (println (str "P: " formatted-pdfs))
    (println (str "Y: " formatted-observations))
    (println (str "E: " final-e))))
