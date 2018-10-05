(ns foppl.autodiff
  "Performs reverse-mode automatic differentiation."
  (:require [foppl.ast :as ast :refer [accept]])
  (:import [foppl.ast definition variable fn-application if-cond])
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

(def f2
  '(fn [x y] (+ (* x x) (sin x))))

(def f3
  '(fn [x] (if (> x 5) (* x x) (+ x 18))))

(def f4
  '(fn [x] (log x)))

(def f5
  '(fn [x mu sigma] (+ (- 0 (/ (* (- x mu) (- x mu))
                              (* 2 (* sigma sigma))))
                      (* (- 0 (/ 1 2)) (log (* 2 (* 3.141592653589793 (* sigma sigma))))))))

(def f6
  '(fn [x mu sigma] (normpdf x mu sigma)))

(def f7
  '(fn [x1 x2 x3] (+ (+ (normpdf x1 2 5)
                       (if (> x2 7)
                         (normpdf x2 0 1)
                         (normpdf x2 10 1)))
                    (normpdf x3 -4 10))))

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

;; an equation is an element of the tape that is produced by
;; traversing a function's definition and building its corresponding
;; computational graph. An equation associates a unique name to a
;; function application, represented by the AST node defined in
;; `foppl.ast`. Every name in a tape is unique.
(defrecord equation [name n])

;; the flow-graph-visitor is responsible for traversing the definition
;; of the function that is being differentiated. Its goal is to build
;; a "tape" (or Wengert List) that represents the sequence of
;; computational steps that take place in a function.
(defrecord flow-graph-visitor [tape params])

(defn- constant-equation [n]
  "Helper function that builds an equation representing a constant
  value."
  (equation. (str (ast/fresh-sym "const")) n))

(defn- arg-equation [n]
  "Helper function that builds an equation representing a reference to
  a parameter of the function"
  (equation. (str (ast/fresh-sym "arg")) n))

(defn- fn-equation [name args]
  "Helper function to create an equation associated with a certain
  function application."
  (equation. (str (ast/fresh-sym "z")) (ast/fn-application. name args)))

(defn- if-equation [predicate then else]
  "Helper function to create an equation associated with a conditional
  in the definition of the function being derived."
  (equation. (str (ast/fresh-sym "z")) (ast/if-cond. predicate then else)))

(defn- volatile-equation? [{name :name}]
  "Volatile equations are created during intermediary steps in the
  process of building a function's computational graph. More
  specifically, these are constant and parameter reference
  equations. These are not included in the final Wengert list
  representation of a function, and this function can be used as a
  predicate on a tape to filter these equations."
  (let [sname (str name)]
    (or (s/starts-with? sname "arg") (s/starts-with? sname "const"))))

(defn- append-equations [eqs {tape :tape params :params}]
  "Given a collection of equations `eqs`, this function will create a
  new visitor appending the given equations to the end of the tape."
  (let [new-tape (into tape eqs)]
    (flow-graph-visitor. new-tape params)))

(defn- append-equation [eq v]
  "Helper function to append a single equation to the end of the
  tape."
  (append-equations [eq] v))

(defn- accept-coll [coll v]
  "Visits a collection of AST nodes in sequence, with a potentially
  different tape after each visit."
  (let [build-graph (fn [v n] (accept n v))]
    (reduce build-graph v coll)))

(extend-type flow-graph-visitor
  ast/visitor

  (visit-constant [v c]
    ;; constants add a temporary "constant equation" in the tape. It
    ;; is ultimately removed from the tape by the enclosing function
    ;; application
    (->> v
         (append-equation (constant-equation c))))

  (visit-variable [{params :params :as v} {name :name :as var}]
    ;; if the variable being referenced is not in the list of function
    ;; parameters, raise an error (the function definition is
    ;; invalid).
    (when-not (contains? params name)
      (utils/foppl-error (str "autodiff error: undefined variable " name)))

    ;; variables, much like constants, add temporary "arg equation" in
    ;; the tape.  They are also ultimately removed if used within a
    ;; function application.
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

  (visit-if-cond [{params :params :as v} {predicate :predicate then :then else :else}]
    (let [;; visit each branch of this condition with empty tapes
          empty-v (flow-graph-visitor. [] params)
          {then-tape :tape} (accept then empty-v)
          {else-tape :tape} (accept else empty-v)

          ;; helper function to transform the resulting equation of
          ;; each branch of the conditional into an AST node. The
          ;; resulting equation is the last equation in the tape.
          to-ast (fn [tape] (let [final-eq (last tape)
                                 {name :name n :n} final-eq]
                             (if (volatile-equation? final-eq)
                               n
                               (ast/variable. name))))

          ;; AST nodes representing each branch of the conditional
          then-ast (to-ast then-tape)
          else-ast (to-ast else-tape)

          ;; merge both tapes -- equations for both will need to be
          ;; added to the resulting tape of this `if`
          ;; expression. Filter those that are volatile and should not
          ;; be included
          both-tapes (into then-tape else-tape)
          branches-eqs (into [] (filter (comp not volatile-equation?) both-tapes))

          ;; create an equation for the `if` expression. The predicate
          ;; remains unchanged, but the `then` and `else` clauses were
          ;; computed above
          if-eq (if-equation predicate then-ast else-ast)

          ;; the equations that should be added to the tape as a
          ;; result of an `if` expression are those resulting from the
          ;; computations performed in each branch, plus the `if`
          ;; expression equation itself.
          new-equations (conj branches-eqs if-eq)]

      (append-equations new-equations v)))

  (visit-fn-application [{params :params :as v} {name :name args :args}]
    (let [ ;; build a tape from scratch for each of the arguments of the function
          empty-v (flow-graph-visitor. [] params)
          args-vs (map (fn [n] (accept n empty-v)) args)
          args-tapes (map :tape args-vs)

          ;; each function argument ends up having an equation
          ;; representing the final result of its computation
          all-args-eqs (doall (map last args-tapes))

          ;; the `args-tape` tape above should have one equation for
          ;; each argument passed to this function. However, not all
          ;; equations are ultimately needed in the final, resulting
          ;; tape. In particular, "volatile equations" are discarded.
          ;; This function maps equations in the arguments tape into
          ;; corresponding AST nodes.  If the equation is volatile, it
          ;; is safe to associate the variable/constant node
          ;; directly. Otherwise, the corresponding AST node should be
          ;; a new variable node pointing to the name of the equation
          ;; being introduced.
          eq-to-ast(fn [{name :name n :n :as eq}] (if (volatile-equation? eq)
                                                   n
                                                   (ast/variable. name)))
          fn-args (map eq-to-ast all-args-eqs)

          ;; add to the tape only the argument-related equations that
          ;; are not volatile
          args-equations (into [] (filter (comp not volatile-equation?) (flatten args-tapes)))

          ;; every function application creates a new equation on the
          ;; tape.
          fn-eq (fn-equation name fn-args)

          ;; finally, the collection of equations being introduced by
          ;; a function application is the collection of equation
          ;; introduced by each argument passed to the function, plus
          ;; the equation representing the function application
          ;; itself.
          new-equations (conj args-equations fn-eq)]

      (append-equations new-equations v)))

  (visit-sample [v {dist :dist}]
    (utils/foppl-error "autodiff error: sample call"))

  (visit-observe [v {dist :dist val :val}]
    (utils/foppl-error "autodiff error: observe call"))
  )

(defn- compute-graph [{args :args e :e}]
  "Builds the computational graph (or 'tape', or Wengert list)
  associated with a function's definition. Returns a collection of
  equations."
  (let [v (flow-graph-visitor. [] (set args))]
    (:tape (accept e v))))

(defn- generate-autodiff [tape] tape)

(defn- serialize [node] node)

(defn perform [f]
  "Performs automatic, reverse-mode diferentiation of a function
  `f`. The function should be passed in quoted form. Returns another
  function that, when invoked with the correct number of parameters,
  returns the result of applying `f` with those parameters, and a map
  of partial derivatives for each function parameter."
  (-> f
      to-tree
      compute-graph
      generate-autodiff
      serialize))
