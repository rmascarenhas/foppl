(ns foppl.operations
  "Provides functions that manipulate the result of the compilation of a
  FOPPL program into an internal representation of a graphical model."
  (:require [foppl.formatter :as formatter]
            [foppl.ast :as ast :refer [accept]]
            [clojure.string :as s]))

(defn count-vertices [{graph :G}]
(count (:V graph)))

(defn count-edges [{graph :G}]
(count (:A graph)))

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
