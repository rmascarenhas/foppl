(ns foppl.toposort
  "Performs topological sort of an acyclic graph."
  (:require [clojure.set :as set]))

;; Based on Alan Dipert's original implementation
;;     https://gist.github.com/alandipert/1263783

(defn- without
  "Returns set s with x removed."
  [s x] (set/difference s #{x}))

(defn- take-1
  "Returns the pair [element, s'] where s' is set s with element removed."
  [s] {:pre [(not (empty? s))]}
  (let [item (first s)]
    [item (without s item)]))

(defn- no-incoming
  "Returns the set of nodes in graph g for which there are no incoming
  edges, where g is a map of nodes to sets of nodes."
  [g]
  (let [nodes (set (keys g))
        have-incoming (apply set/union (vals g))]
    (set/difference nodes have-incoming)))

(defn- normalize
  "Returns g with empty outgoing edges added for nodes with incoming
  edges only.  Example: {:a #{:b}} => {:a #{:b}, :b #{}}"
  [g]
  (let [have-incoming (apply set/union (vals g))]
    (reduce #(if (get % %2) % (assoc % %2 #{})) g have-incoming)))

(defn- toposort
  "Proposes a topological sort for directed graph g using Kahn's
   algorithm, where g is a map of nodes to sets of nodes. If g is
   cyclic, returns nil."
  ([g]
   (toposort (normalize g) [] (no-incoming g)))
  ([g l s]
   (if (empty? s)
     (when (every? empty? (vals g)) l)
     (let [[n s'] (take-1 s)
           m (g n)
           g' (reduce #(update-in % [n] without %2) g m)]
       (recur g' (conj l n) (set/union s' (set/intersection (no-incoming g') m)))))))

(defn perform [{{A :A} :G}]
  "Performs topological sort of a graphical model, given as a
  foppl.graphical.model record. Returns an array of random-variable
  names that representa topological sort of the graph."
  (let [sources (map (fn [[from to]] from) A)
        graph (zipmap sources (repeat #{}))
        combine (fn [g [from to]] (assoc g from (conj (get g from) to)))
        graph (reduce combine graph A)]
    (toposort graph)))
