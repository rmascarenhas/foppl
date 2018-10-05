(ns foppl.autodiff
  "Performs reverse-mode automatic differentiation."
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast definition variable fn-application])
  (:require [foppl.utils :as utils])
  (:require [clojure.string :as s])
  (:require [anglican.runtime :refer [exp sin cos]]))

;; NUMERICAL APPROXIMATIONS -- TEMPORARILY HERE

(defn addd [exprl i d]
  (if (= i 0)
    (reduce conj [`(~'+ ~d ~(first exprl))] (subvec exprl 1))
    (reduce conj (subvec exprl 0 i)
            (reduce conj [`(~'+ ~d ~(get exprl i))] (subvec exprl (+ i 1))))))

(defn finite-difference-expr [expr args i d]
  `(~'/ (~'- (~expr ~@(addd args i d)) (~expr ~@args)) ~d))

(defn finite-difference-grad [expr]
  (let [[op args body] expr
        d (gensym)
        fdes (map #(finite-difference-expr expr args % d) (range (count args)))
        argsyms (map (fn [x] `(~'quote ~x)) args)]
    `(~'fn [~@args]
      (~'let [~d 0.001]
       ~(zipmap argsyms fdes)))))

;; ----------------------------------------------

;; Derivatives of the supported functions of this auto differentiation library
(def ^:private derivatives
  {'* [(fn [a b] b) (fn [a b] a)]
                                        ; f(a,b) = a * b <-> (* a b)
                                        ; df/da = b
                                        ; df/db = a
   '- [(fn [a b] 1) (fn [a b] -1)]
                                        ; f(a,b) = a - b <-> (- a b)
                                        ; df/da = 1
                                        ; df/db = -1

   '+ [(fn [a b] 1) (fn [a b] 1)]
                                        ; f(a,b) = a + b <-> (+ a b)
                                        ; df/da = 1
                                        ; df/db = 1

   '/ [(fn [a b] (/ 1 b)) (fn [a b] (* a (/ -1 (* b b))))]
                                        ; f(a,b) = a / b <-> (/ a b)
                                        ; df/da = 1
                                        ; df/db = -1/b^2

   'exp [(fn [a] (exp a))]
                                        ; f(a) = (exp a)
                                        ; df/da = (exp a)

   'relu [(fn [a] (if (> a 0) 1 0))]
                                        ; f(a) = (relu a)
                                        ; df/da = 1 if a > 0, 0 otherwise

   'log [(fn [n] nil)]

   'normpdf (fn [n] nil)


   'sin [(fn [a] (cos a))]

   'cos [(fn [a] (sin a))]})

;; Example functions
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

(defrecord equation [name n])


(defrecord flow-graph-visitor [tape params])

(defn- constant-equation [n]
  (equation. (str (ast/fresh-sym "const")) n))

(defn- arg-equation [n]
  (equation. (str (ast/fresh-sym "arg")) n))

(defn- fn-equation [name args]
  (equation. (str (ast/fresh-sym "z")) (ast/fn-application. name args)))

(defn- volatile-equation? [{name :name}]
  (let [sname (str name)]
    (or (s/starts-with? sname "arg") (s/starts-with? sname "const"))))

(defn- append-equations [eqs {tape :tape params :params}]
  (let [new-tape (into tape eqs)]
    (flow-graph-visitor. new-tape params)))

(defn- append-equation [eq v]
  (append-equations [eq] v))

(defn- accept-coll [coll v]
  (let [build-graph (fn [v n] (accept n v))]
    (reduce build-graph v coll)))

(extend-type flow-graph-visitor
  ast/visitor

  (visit-constant [v c]
    (->> v
         (append-equation (constant-equation c))))

  (visit-variable [{params :params :as v} {name :name :as var}]
    (when-not (contains? params name)
      (utils/foppl-error (str "autodiff error: undefined variable " name)))

    (->> v
         (append-equation (arg-equation var))))

  (visit-literal-vector [_ _]
    (utils/foppl-error (str "autodiff error: literal vectors not supported")))

  (visit-literal-map [_ _]
    (utils/foppl-error "autodiff error: literal maps not supported"))

  (visit-definition [_ _]
    (utils/foppl-error "autodiff error: unexpected function definition"))

  (visit-local-binding [_ _]
    (utils/foppl-error "autodiff error: local bindings not supported"))

  (visit-foreach [_ _]
    (utils/foppl-error "autodiff error: foreach not supported"))

  (visit-loop [_ _]
    (utils/foppl-error "autodiff error: loops not supported"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (utils/foppl-error "TODO"))

  (visit-fn-application [{params :params :as v} {name :name args :args}]
    (let [empty-v (flow-graph-visitor. [] params)
          {args-tape :tape} (accept-coll args empty-v)

          eq-to-ast(fn [{name :name n :n :as eq}] (if (volatile-equation? eq)
                                                   n
                                                   (ast/variable. name)))

          fn-args (map eq-to-ast args-tape)
          args-equations (into [] (filter (comp not volatile-equation?) args-tape))
          fn-eq (fn-equation name fn-args)

          new-equations (conj args-equations fn-eq)]

      (append-equations new-equations v)))

  (visit-sample [v {dist :dist}]
    (utils/foppl-error "autodiff error: sample call"))

  (visit-observe [v {dist :dist val :val}]
    (utils/foppl-error "autodiff error: observe call"))
  )

(defn- compute-graph [{args :args e :e}]
  (let [v (flow-graph-visitor. [] (set args))]
    (:tape (accept e v))))

(defn- generate-autodiff [tape] tape)

(defn- serialize [node] node)

(defn diff [f]
  (-> f
      to-tree
      compute-graph
      generate-autodiff
      serialize))
