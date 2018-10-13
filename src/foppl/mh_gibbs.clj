(ns foppl.mh_gibbs
  "Implements Metropolis-within-Gibbs algorithm for the sampling of the
  posterior of the distribution encoded in a graphical model."
  (:require [clojure.set :as set]
            [anglican.runtime :as anglican]
            [foppl.ast :as ast]
            [foppl.eval :as eval]
            [foppl.toposort :as toposort]
            [foppl.utils :as utils])
  (:import [foppl.ast constant fn-application]))

(defn- latent-vars [{V :V Y :Y}]
  (set/difference V (set (keys Y))))

(defn- sample [dist]
  (anglican/sample* dist))

(defn- log-prob [dist v]
  (anglican/observe* dist v))

;; proposal: AST node (normal mu sigma)
;; xs {x1 c1 x2 c2}
(defn- eval-proposal [proposal xs]
  (let [vars (keys xs)
        constant-for (fn [name] (ast/constant. (get xs name)))
        substitute (fn [e name] (ast/substitute name (constant-for name) e))
        bound-proposal (reduce substitute proposal vars)
        const-dist (eval/peval bound-proposal)]
    (:n const-dist)))

(defn- choose-proposal [{V :V P :P Y :Y} proposals x xs xs']
  (let [d (eval-proposal (get proposals x) xs)
        d' (eval-proposal (get proposals x) xs')
        _ (when-not d' (utils/ice "Cannot build new proposed distribution"))

        c (get xs x)
        c' (get xs' x)
        log-a (- (log-prob d' c) (log-prob d c'))

        node-free-vars (fn [name] (ast/free-vars (get P name)))
        free-vars (zipmap V (map node-free-vars V))

        dependence (fn [s v] (if (contains? (get free-vars v) x) (set/union s #{v}) s))
        Vx (reduce dependence #{} V)

        s (fn [e] (foppl.formatter/to-str e))
        substitute-coll (fn [e subs] (reduce
                                     (fn [e [name const]] (ast/substitute name (ast/constant. const) e))
                                     e
                                     subs))

        pdf-at (fn [pdf values] (let [{name :name args :args} (substitute-coll pdf values)
                                     evaluated-args (map eval/peval args)
                                     pdf-fn (ast/fn-application. name evaluated-args)]
                                 (:n (eval/peval pdf-fn))))

        evaluate-proposals (fn [log-a v] (let [pdf (get P v)
                                              observations (zipmap (keys Y) (map :n (vals Y)))
                                              current-vals (merge observations xs)
                                              proposed-vals (merge observations xs')
                                              current-pdf (pdf-at pdf current-vals)
                                              proposed-pdf (pdf-at pdf proposed-vals)]
                                          (- (+ log-a proposed-pdf) current-pdf)))
        log-a (reduce evaluate-proposals log-a Vx)
        a (Math/exp log-a)

        u (rand)]
    (if (< u a) xs' xs)))

(defn- handle-var [graph proposals decide xs x]
  (let [proposed-dist (eval-proposal (get proposals x) xs)
        _ (when-not proposed-dist (utils/ice "Cannot build proposed distribution"))

        xs' xs
        xs' (assoc xs x (sample proposed-dist))]
    (decide x xs xs')))

(defn- gibbs-step [{graph :G :as model} xs proposals]
  (let [latent (latent-vars graph)
        ordering (toposort/perform model)
        unobserved? (partial contains? latent)
        random-vars (filter unobserved? ordering)
        decide (partial choose-proposal graph proposals)
        propose-accept (partial handle-var graph proposals decide)]
    (reduce propose-accept xs random-vars)))

(defn perform [{{A :A Y :Y P :P :as graph} :G :as model}]
  ;; build proposals map
  ;; build initial values
  ;; burn-in
  ;; construct lazy seq of gibbs-step
  (let [latent (latent-vars graph)
        with-latent (partial zipmap latent)
        extract-dist (fn [x] (first (:args (get P x))))
        link-fns (map extract-dist latent)
        proposals (with-latent link-fns)
        xs (with-latent (repeat 1.0))
        samples (reduce
                 (fn [{xs :xs data :data} _]
                   (let [xs (gibbs-step model xs proposals)]
                     {:xs xs :data (conj data xs)}))
                 {:xs xs :data []}
                 (repeat 50 nil))]
    model))
