(ns foppl.autodiff
  "Performs reverse-mode automatic differentiation."
  (:require [foppl.ast :as ast :refer [accept]])
  (:require [foppl.desugar :as desugar])
  (:import [foppl.ast definition constant variable fn-application if-cond literal-map literal-vector local-binding])
  (:require [foppl.formatter :as formatter])
  (:require [foppl.utils :as utils])
  (:require [clojure.string :as s])
  (:require [clojure.edn :as edn])
  (:require [anglican.runtime :as anglican :refer [exp log sin cos]]))

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

(defn normpdf [y mu sigma]
  (anglican/observe* (anglican/normal mu sigma) y))

;; Derivatives of the supported functions of this auto differentiation library
(def ^:private derivatives
  {'* ['(fn [a b] b) '(fn [a b] a)]
                                        ; f(a,b) = a * b <-> (* a b)
                                        ; df/da = b
                                        ; df/db = a
   '- ['(fn [a b] 1) '(fn [a b] -1)]
                                        ; f(a,b) = a - b <-> (- a b)
                                        ; df/da = 1
                                        ; df/db = -1

   '+ ['(fn [a b] 1) '(fn [a b] 1)]
                                        ; f(a,b) = a + b <-> (+ a b)
                                        ; df/da = 1
                                        ; df/db = 1

   '/ ['(fn [a b] (/ 1 b)) '(fn [a b] (* a (/ -1 (* b b))))]
                                        ; f(a,b) = a / b <-> (/ a b)
                                        ; df/da = 1
                                        ; df/db = -1/b^2

   'exp ['(fn [a] (exp a))]
                                        ; f(a) = (exp a)
                                        ; df/da = (exp a)

   'relu ['(fn [a] (if (> a 0) 1 0))]
                                        ; f(a) = (relu a)
                                        ; df/da = 1 if a > 0, 0 otherwise

   'log ['(fn [n] (/ 1 n))]

   'normpdf ['(fn [x m s] (let [m-x (- m x)
                               s2 (* s s)
                               s3 (* s2 s)
                               m-x2 (* m-x m-x)
                               exponent (- (/ m-x2 (* 2 s2)))]
                           (/ (* m-x (exp exponent)) (* (anglican/sqrt (* 2 Math/PI)) s3))))

             '(fn [x m s] (let [x-m (- x m)
                               m-x (- m x)
                               s2 (* s s)
                               s3 (* s2 s)
                               m-x2 (* m-x m-x)
                               exponent (- (/ m-x2 (* 2 s2)))]
                           (/ (* x-m (exp exponent)) (* (anglican/sqrt (* 2 Math/PI)) s3))))

             '(fn [x m s] (let [m-x (- m x)
                               s-x+u (+ (- s x) u)
                               s+x-u (- (+ s x) u)
                               s2 (* s s)
                               s4 (* s2 s2)
                               m-x2 (* m-x m-x)
                               exponent (- (/ m-x2 (* 2 s2)))]
                           (- (/ (* s-x+u s+x-u (exp exponent)) (* anglican/sqrt (* 2 Math/PI) s4)))))
             ]


   'sin ['(fn [a] (cos a))]

   'cos ['(fn [a] (sin a))]})

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

  (let [args (map ast/to-tree (second f))
        e (last f)
        parsed-e (ast/to-tree e)
        {e :e} (desugar/perform {:defs nil :e parsed-e})]
    (ast/definition. nil args e)))

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

  (visit-literal-map [_ m]
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

;; `delta-visitor` is responsible for visiting an equation
;; (represented as a function application or an `if` conditional) and
;; calculating a collection of bindings to be used in the
;; derivative-generating function. Only functions whose derivatives
;; are known (i.e., declared in the `derivatives` map) are calculated.
(defrecord delta-visitor [name delta])

(extend-type delta-visitor
  ast/visitor

  (visit-constant [_ c]
    ;; visiting a constant returns `nil`. The caller (a function
    ;; application) will then be able to identify that no derivative
    ;; binding is necessary.
    nil)

  (visit-variable [_ var]
    ;; if a variable is used in a function application, its partial
    ;; derivative needs to be calculated (and added to the collection
    ;; of bindings)
    var)

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

  (visit-fn-application [{name :name delta :delta :as v} {f :name args :args}]
    (let [ ;; given a function's name, this will return a collection of
          ;; partial derivatives with respect to each parameter the
          ;; function takes. Partial derivatives are defined in the
          ;; `derivatives` collection. If derivates are not known for
          ;; the function given, this will throw an exception.
          derivatives-for (fn [name] (doto (get derivatives name)
                                      (when-not (utils/foppl-error (str "autodiff error: no know derivative for: " name)))))

          ;; collection of partial derivatives for the function being applied
          ds (derivatives-for f)

          ;; given an index to the collection of parameters a function
          ;; takes, this will return an AST representation of the
          ;; partial derivative with respect to the i-th parameter of
          ;; the function being applied.
          derivative-at (fn [i] (let [lambda (get ds i)] (to-tree lambda)))

          ;; combines two collections: (zip [a1 a2 a3] [b1 b2 b3]) => [[a1 b1] [a2 b2] [a3 b3]]
          zip (fn [coll1 coll2] (mapv vector coll1 coll2))

          ;; given an expression and a name->expression pair, this
          ;; will substitute name for n in e and return the resulting
          ;; expression
          substitute-name (fn [e [name n]] (ast/substitute name n e))

          ;; given the definition of a partial derivative (as an
          ;; anonymous function) and a matching set of arguments, this
          ;; produces an AST node where each pameter is substituted
          ;; for the arguments given
          apply-deriv (fn [{params :args e :e} args] (reduce substitute-name e (zip (map :name params) args)))

          ;; visit each argument passed to the function being applied recursively.
          ;; Note that these are, by construction, either variables or constants.
          variable-args (map (fn [n] (accept n v)) args)

          ;; helper function to build the derivative of a variable (that could be either a function
          ;; parameter or an intermediary result of the computation). `darg` is the AST representation
          ;; of the partial derivative of the function being applied with respect to the variable given.
          ;; The derivative is given by the formula:
          ;;
          ;;     dv = dv + dz * darg(arg1 ... argn)
          e-for (fn [{vname :name} darg]
                  (ast/fn-application. '+ [(delta vname) (ast/fn-application. '* [(delta name) (apply-deriv darg args)])]))

          ;; maps each argument to the function to its partial
          ;; derivative, according to the formula used in the `e-for`
          ;; helper function.
          bindings (map-indexed (fn [i a] (when a [(delta (:name a)) (e-for a (derivative-at i))])) variable-args)

          ;; filter `nil` bindings from the computation above
          ;; (resulting when some of the arguments passed to the
          ;; function are constant values).
          bindings (filter (comp not nil?) bindings)]

      (into [] bindings)))

  (visit-sample [v {dist :dist}]
    (utils/foppl-error "autodiff error: sample call"))

  (visit-observe [v {dist :dist val :val}]
    (utils/foppl-error "autodiff error: observe call"))
  )

;; comp-graph represents a computational graph derived from the
;; structure of a function definition. The parameters remain
;; unchanged, and the tape represents the series of operartions (a
;; collection of equations) that encode the computations that occur in
;; the function.
(defrecord comp-graph [params tape])

(defn- compute-graph [{args :args e :e}]
  "Builds the computational graph (or 'tape', or Wengert list)
  associated with a function's definition. Returns a collection of
  equations."
  (let [v (flow-graph-visitor. [] (set (map :name args)))
        tape (:tape (accept e v))]
    (comp-graph. args tape)))

;; format of the function generated:
;;
;; (fn [arg1 ... argn]
;;   (let [z1 eq1
;;       ....
;;         zn eqn]
;;         darg1 0
;;         ...
;;         dargn 0
;;         dz1 0
;;         ...
;;         dzn 1
;;         dzn (+ ...)
;;         ...]
;;      [zn {arg1 darg1 ... argn dargn]))
;;
;; where z1, ..., zn are the symbols used to identify the equations in
;; the computational graph's tape.
(defn- generate-autodiff [{params :params tape :tape}]
  "Given a computation graph, this function will produce another
  function of the same parameters of the original function that, when
  evaluated and applied to a proper set of arguments, will produce the
  value of the original function applied with the parameters given,
  and a map containing the partial derivatives with respect to each
  function parameter."
  (let [ ;; helper functions: create variable and constant AST nodes;
        ;; create a fresh symbol; and transform a collection into a
        ;; vector (useful to ensure semantics of cons/conj)
        variable (fn [name] (ast/variable. name))
        constant (fn [v] (ast/constant. v))
        new-name (fn [] (ast/fresh-sym "x"))
        to-vec (fn [coll] (into [] coll))
        delta (fn [name] (variable (str "d" name)))
        params-names (map :name params)

        ;; create bindings for each equation defined in the tape
        bind (fn [{name :name n :n}] [(variable name) n])
        tape-bindings (to-vec (map bind tape))

        ;; the list of bindings is a flat collection (with an even
        ;; number of elements).  One of the expressions returned by
        ;; the generated function is the value of the original
        ;; function f applied to the arguments given (forward-mode
        ;; execution), and `final-name` represents the variable
        ;; containing this result.
        bindings (to-vec (flatten tape-bindings))
        final-eq-name (:name (last tape))
        final-name (variable final-eq-name)

        ;; Reverse-mode differentiation
        ;; derivatives of intermediary computation values (as well as
        ;; function parameters) are prefixed with "d".

        ;; helper function to initialize derivatives of a collection
        ;; of names to zero
        init-zero (fn [name] [(delta name) (constant 0)])

        ;; initialize the derivatives of all parameters and tape
        ;; equation names to zero
        delta-params (mapv init-zero params-names)
        delta-tape (mapv init-zero (map :name tape))

        ;; the derivative of the result of the function's computation
        ;; (represented by the last equation in the tape) is
        ;; initialized to 1).
        delta-tape (pop delta-tape)
        delta-final [(delta final-eq-name) (constant 1)]

        ;; combines the bindings above in a single collection
        init-deltas (concat delta-params delta-tape delta-final)

        ;; reverse-mode differentiation works through the tape in
        ;; reverse order
        backwards (reverse tape)

        ;; for each equation in the tape, calculate the set of
        ;; bindings that should be added to this generated
        ;; function. See definition of `delta-visitor` for more
        ;; information on how this happens.
        compute-bindings (fn [{name :name n :n}] (let [v (delta-visitor. name delta)] (accept n v)))
        calculate-derivatives (fn [eq] (compute-bindings eq))
        derivatives (mapv calculate-derivatives backwards)

        ;; bindings related to derivative calculation is the union of
        ;; initialization bindings and derivative calculations
        deriv-bindings (to-vec (concat init-deltas derivatives))
        bindings (concat bindings (flatten deriv-bindings))

        ;; map names to explicit calls to `symbol` such that, when the
        ;; function is ultimately evaluated, the returned map contains
        ;; the name of the parameters as a symbol (instead of trying
        ;; to resolve the names).
        symbolize (fn [a] (ast/fn-application. 'symbol [(constant (str a))]))

        ;; the partial derivatives returned to the caller is a map
        ;; from argument name to the partial derivative of the
        ;; original function `f` with respect to that parameter.
        partial-derivs (ast/literal-map. (mapcat (fn [a] [(symbolize a) (delta a)]) params-names))

        ;; the returned expression of this `let` binding is a vector
        ;; where the first element is the value of the original function
        ;; `f` applied to the arguments given; and the second element
        ;; is a map of partial derivatives.
        e (ast/local-binding. bindings [(ast/literal-vector. [final-name partial-derivs])])]

    (ast/definition. nil params e)))

(defn- serialize [f]
  "Given a function definition represented as an AST node, this
  function will produce a quoted Clojure function definition that can
  be passed around, evaluated and applied to different parameters to
  calculate the partial derivatives with respect to different sets of
  arguments."
  (-> f
      formatter/to-str
      edn/read-string))

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
