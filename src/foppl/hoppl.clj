(ns foppl.hoppl
  "This module implements evaluation-based inference. It extends FOPPL
  by adding higher-order features to it: specifically, HOPPL allows
  the use of anonymous functions and recursion."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.desugar :as desugar]
            [foppl.utils :as utils])
  (:import [foppl.ast constant variable if-cond fn-application literal-vector
            literal-map procedure lambda local-binding sample observe program]))

(defn- accept-coll [coll v]
  "Visits a collection of AST nodes `coll` with visitor `v`."
  (let [perform (fn [n] (accept n v))]
    (map perform coll)))

;; loop-desugar-visitor is responsible for desugaring `loop` forms in HOPPL programs. Loops
;; in HOPPL are equivalent to a `let` expression which then applies the `loop-helper`
;; function (see definition in `foppl.primitives`).
(defrecord loop-desugar-visitor [])

(extend-type loop-desugar-visitor
  ast/visitor

  (visit-constant [_ c]
    c)

  (visit-variable [_ var]
    var)

  (visit-literal-vector [v {es :enns}]
    (ast/literal-vector. (accept-coll es v)))

  (visit-literal-map [v {es :es}]
    (ast/literal-map. (accept-coll es v)))

  (visit-procedure [v {name :name args :args e :e}]
    (ast/procedure. name args (accept e v)))

  (visit-lambda [v {name :name args :args e :e}]
    (ast/lambda. name args (accept e v)))

  (visit-local-binding [v {bindings :bindings es :es}]
    (let [pairs (partition 2 bindings)

          ;; loop desugaring is the first to be performed. Local
          ;; bindings may still include multiple bindings in a single
          ;; `let` form, so we desugar every pair.
          desugar-pair (fn [[name e]] [name (accept e v)])
          desugared-bindings (mapcat desugar-pair pairs)]

      (ast/local-binding. desugared-bindings (accept-coll es v))))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (let [;; helper functions to create variable and constant AST nodes
          variable (fn [name] (ast/variable. name))
          constant (fn [c] (ast/constant. c))

          ;; for each expression to e1, e2, ..., en passed to `loop`,
          ;; generate a fresh symbol for it
          bound-names (repeatedly (count es) #(variable. (ast/fresh-sym)))

          ;; bind each expression to the symbols generated
          bound-es (into [] (mapcat vector bound-names es))

          ;; the `g` function is an anonymous function that is used in
          ;; the `loop-helper` function, made available by HOPPL.
          g (ast/lambda. nil
                         [(variable 'i) (variable 'w)]
                         (ast/fn-application. f (into [(variable 'i) (variable 'w)] bound-names)))

          ;; all bindings in the desugared `let` corresponding to the
          ;; HOPPL `loop`.  See the book for a better diagram of the
          ;; desugaring process.
          bindings (into [(variable 'bound) c (variable 'initial-value) e] (into bound-es [(variable 'g) g]))

          e (ast/fn-application. 'loop-helper [(constant 0) (variable 'bound) (variable 'initial-value) (variable 'g)])]

      (ast/local-binding. bindings [e])))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (ast/if-cond. (accept predicate v) (accept then v) (accept else v)))

  (visit-fn-application [v {name :name args :args}]
    (ast/fn-application. name (accept-coll args v)))

  (visit-sample [v {dist :dist}]
    (ast/sample. (accept dist v)))

  (visit-observe [v {dist :dist val :val}]
    (ast/observe. (accept dist v) (accept val v))))

(defn- desugar-loops [{defs :defs e :e}]
  "Desugars `loop` constructs in HOPPl (which work differently from
  their FOPPL counterparts)."
  (let [v (loop-desugar-visitor.)
        desugar (fn [n] (accept n v))]
    (ast/program. (map desugar defs) (accept e v))))

(defn- desugar-let [{defs :defs e :e :as program}]
  "`let` expressions are just sugar in HOPPL: they get translated to
  anonymous function applications."
  program)

(defn- desugar [program]
  "Desugars a HOOPL program entirely: loops are desugared into `let`
  bindings; `let` bindings with multiple bindings are desugared to
  `let` forms with a single binding; and finally `let` expressions are
  removed altogether and replaced with the application of anonymous
  functions."
  (-> program
      desugar-loops
      desugar/multiple-bindings
      desugar-let))

(defn- interpret [program]
  program)

(defn perform [program]
  "Performs evaluation-based inference of a HOPPL program. First, the
  program is desugared, then it is interpreted. Inference uses
  importance sampling."
  (-> program
      desugar
      interpret))
