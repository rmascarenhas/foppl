(ns foppl.mh_gibbs
  "Implements the Metropolis-within-Gibbs algorithm for the sampling of
  the posterior of the distribution represented by a graphical model."
  (:require [clojure.set :as set]
            [anglican.runtime :as anglican]
            [foppl.ast :as ast :refer [accept]]
            [foppl.eval :as eval]
            [foppl.toposort :as toposort]
            [foppl.utils :as utils])
  (:import [foppl.ast constant fn-application]))

;; evaluates a function expression recursively until it can ultimately
;; be represented as a constant value. Basically wraps calls to
;; `eval/peval`, which only applies functions if all arguments are
;; constants (which is the case during graphical model compilation,
;; but not here).
(defrecord deep-eval-visitor [])

(extend-type deep-eval-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [_ literal-vector]
    literal-vector)

  (visit-literal-map [_ literal-map]
    literal-map)

  (visit-definition [_ definition]
    definition)

  (visit-local-binding [_ local-binding]
    local-binding)

  (visit-foreach [_ foreach]
    foreach)

  (visit-loop [_ loop]
    loop)

  (visit-if-cond [_ if-cond]
    (if-cond))

  (visit-fn-application [v {name :name args :args}]
    (let [evaluated-args (map (fn [n] (accept n v)) args)
          f (ast/fn-application. name evaluated-args)]
      (eval/peval f)))

  (visit-sample [_ sample]
    sample)

  (visit-observe [_ observe]
    observe)
  )

(defn- latent-vars [{V :V Y :Y}]
  "Given the graph component of a graphical model, this function
  returns the set of latent functions of the graph (i.e., the set of
  vertices that were not observed."
  (set/difference V (set (keys Y))))

(defn- sample [dist]
  "Samples from a standard distribution. Relies on Anglican's
  implementation of sampling. The `dist` parameter should be an
  Anglican distributiob object."
  (anglican/sample* dist))

(defn- log-prob [dist v]
  "Calculates the log-probability of `dist` and value `v`. Relies on
  Anglican's implementation."
  (anglican/observe* dist v))

(defn- eval-proposal [proposal xs]
  "Evaluates a `proposal`, given as an AST representation of a
  distribution expression, under the map of random variable values
  `xs`. In other words, each random variable in the `proposal`
  expression is substituted for its corresponding value in the `xs`
  maop, and the expression is then evaluated. The function returns an
  Anglicna distribution object that results from the evaluation."
  (let [vars (keys xs)

        ;; helper function to construct a constant AST node for a
        ;; random-variable with the name given, based on its value in
        ;; the `xs` map.
        constant-for (fn [name] (ast/constant. (get xs name)))
        substitute (fn [e name] (ast/substitute name (constant-for name) e))

        ;; substitute each random-variable in `xs` in the `proposal`
        ;; expression.  The resulting expression should have no free
        ;; variables at the end of this process.
        bound-proposal (reduce substitute proposal vars)
        const-dist (eval/peval bound-proposal)]

    ;; return the raw Anglican distribution object from the evaluation
    (:n const-dist)))

(defn- choose-proposal [{V :V P :P Y :Y} proposals x xs xs']
  "This function decides whether to accept a new assignment of random
  variables `xs'` or to maintain the current assignment `xs`. The
  first argument is the graph component of a graphical model, and
  `proposals` is a map of proposal distributions mapping from
  random-variable name to its proposed distribution (given as an AST
  node). Returns either `xs` or `xs'`. For more extensive information
  on how the algorithm works, check section 3.3 of the Introduction to
  Probabilistic Programming book."
  (let [ ;; evaluate resulting proposal distributions based on existing
        ;; and proposed set of assignments.
        d (eval-proposal (get proposals x) xs)
        d' (eval-proposal (get proposals x) xs')

        ;; Validation step: `d` and `d'` should both be distribution
        ;; objects
        _ (when-not d' (utils/ice "Cannot build new proposed distribution"))

        ;; log-a is the log probability of the alpha component, which
        ;; is used to decide whether to accept or reject the proposed
        ;; set of assignments
        c (get xs x)
        c' (get xs' x)
        log-a (- (log-prob d' c) (log-prob d c'))

        ;; calculate a map from {random-variable name -> set of free
        ;; variables in its link function}.
        node-free-vars (fn [name] (ast/free-vars (get P name)))
        free-vars (zipmap V (map node-free-vars V))

        ;; Vx is the Markov Blanket of random variable `x`. In terms
        ;; of a graphical model representation, this set consists of
        ;; all vertices `v` in the graph where `x` is free in the link
        ;; function of `v`.
        dependence (fn [s v] (if (contains? (get free-vars v) x) (set/union s #{v}) s))
        Vx (reduce dependence #{} V)

        ;; given an expression `e`, this performs a sequence of
        ;; substitutions based on the `subs` map from names to
        ;; constants. Returns the resulting expression
        substitute-coll (fn [e subs] (reduce
                                     (fn [e [name const]] (ast/substitute name (ast/constant. const) e))
                                     e
                                     subs))

        ;; This function takes an AST node representing the PDF of a
        ;; certain distribution and a map of values, and then returns
        ;; the distribution object obtained by performing the
        ;; substitutions contained in `values` and evaluating the
        ;; resulting exression
        pdf-at (fn [pdf values] (let [f (substitute-coll pdf values)
                                     dist-constant (accept f (deep-eval-visitor.))]
                                 (:n dist-constant)))

        ;; this function is responsible for calculating the log-a
        ;; component according to the formula that defines the
        ;; Metropolis-within-Gibbs algorithm.
        evaluate-proposals (fn [log-a v] (let [ ;; the PDF function associated with vertex `v`
                                              pdf (get P v)

                                              ;; maps observed random variables names to the raw
                                              ;; constant value that was observed
                                              observations (zipmap (keys Y) (map :n (vals Y)))

                                              ;; calculate current and proposed map of random
                                              ;; variable assignments
                                              current-vals (merge observations xs)
                                              proposed-vals (merge observations xs')

                                              ;; evaluate PDF according to current and proposed
                                              ;; random variable assignments
                                              current-pdf (pdf-at pdf current-vals)
                                              proposed-pdf (pdf-at pdf proposed-vals)]

                                          ;; return the corresponding updated log-a value
                                          (- (+ log-a proposed-pdf) current-pdf)))

        ;; perform the update of log-a for each vertex in `Vx`
        log-a (reduce evaluate-proposals log-a Vx)

        ;; obtain the value of the alpha component from `log-a`
        a (Math/exp log-a)

        ;; sample from a Uniform(0, 1) distribution
        u (rand)]

    ;; decide between current and proposed states
    (if (< u a) xs' xs)))

(defn- handle-var [graph proposals decide xs x]
  "Updates random variable assignment for a single random variable `x`
  in the set of latent variables `xs` and decides whether the update
  should be accepted or rejected (see actual decision procedure in
  `choose-proposal`. The `decide` argument should be a decision
  function that, when applied with arguments 1) random variable `x`;
  2) current assignment `xs`; and 3) proposed assignment `xs'`, should
  return either one of `xs` or `xs'`. Returns either `xs` or an
  updated assignment of random variables."
  (let [proposed-dist (eval-proposal (get proposals x) xs)

        ;; validation step: make sure the proposal distribution
        ;; evaluated to a valid distribution object
        _ (when-not proposed-dist (utils/ice "Cannot build proposed distribution"))

        ;; propose new assignment of random variables by updating
        ;; entry on variable `x`
        xs' (assoc xs x (sample proposed-dist))]
    (decide x xs xs')))

(defn- gibbs-step [{graph :G :as model} xs proposals]
  "Performs one step of a Gibbs sampling algorithm. The algorithm
  updates the assignments for one latent variable at a time and
  decides whether the proposed assignment should be accepted or
  rejected. The `xs` argument should be the initial assignment of
  random-variables. The `proposals` argument is a map from random
  variable names to proposal distributions, represented as AST
  nodes (possibly with free variables)."
  (let [;; calculate the set of latent variables in the graph given
        latent (latent-vars graph)

        ;; variables should be handled in topological order.
        ordering (toposort/perform model)

        ;; random-variables to be considered should be those that were
        ;; not observed in the model, in the topological order
        ;; calculated above
        unobserved? (partial contains? latent)
        random-vars (filter unobserved? ordering)

        ;; the decision function is `choose-proposal`, partially
        ;; applied with the graph and proposals map already known at
        ;; this point.
        decide (partial choose-proposal graph proposals)

        ;; function invoved for each of the random variables that
        ;; compute a proposed set of random-variable assignments and
        ;; decide whether to accept or reject it.
        propose-accept (partial handle-var graph proposals decide)]

    ;; iterate over random variables, with initial assignment
    ;; `xs`. Returns the updated random-variable assignment.
    (reduce propose-accept xs random-vars)))

(defn- gibbs-lazy-seq [initial gen-fn]
  "Generates a lazy sequence for an initial map of
  assignments. `gen-fn` is supposed to be a function that takes a map
  of assignments, and returns an updated map of assignments as a
  result of running a single step of the Gibbs algorithm."
  (let [next (gen-fn initial)]
    (lazy-seq (cons next (gibbs-lazy-seq next gen-fn)))))

(defn perform [{{A :A Y :Y P :P :as graph} :G :as model}]
  "Performs sampling of the posterior distribution of latent variables
  represented by a graphical model. Returns a lazy sequence of samples
  from the posterior."
  (let [latent (latent-vars graph)

        ;; helper function to create maps from latent variables to
        ;; some value
        with-latent (partial zipmap latent)

        ;; extracts distribution AST node from a link function (which
        ;; should be in the format (observe* dist val)
        extract-dist (fn [x] (first (:args (get P x))))

        ;; link functions for each of the latent variables in the
        ;; model
        link-fns (map extract-dist latent)

        ;; set of proposed distributions are the link functions in the
        ;; graphical model
        proposals (with-latent link-fns)

        ;; initial random-variable assignment to get the process
        ;; started
        xs (with-latent (repeat 0.0))

        ;; run the Metropolis-within-Gibbs algorithm for `n`
        ;; iterations, given the initial assignment of random
        ;; variables `xs`. Returns a map with keys `:xs` and `:data`,
        ;; where `xs` is the assignment map for the last iteration,
        ;; and `data` is a vector containing the assignments for every
        ;; iteration of the algorithm.
        gibbs (fn [n xs]
                (reduce
                 (fn [{xs :xs data :data} _]
                   (let [xs (gibbs-step model xs proposals)]
                     {:xs xs :data (conj data xs)}))
                 {:xs xs :data []}
                 (repeat n nil)))

        ;; burn-in state: run the algorithm a number of times to make
        ;; sure we get a set of variable assignments that are "within"
        ;; the posterior distribution
        {burned-in :xs} (gibbs 10000 xs)

        ;; the `gibbs` helper function defined above is a lot more
        ;; general and is able to run `n` gibbs steps. However, in
        ;; order to generate our lazy sequence, we write a wrapper for
        ;; it that, given a map of assignments, produces a new map of
        ;; assignments as a result of running a single gibbs step
        next-sample (fn [xs] (:xs (gibbs 1 xs)))]

    (gibbs-lazy-seq burned-in next-sample)))
