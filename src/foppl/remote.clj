(ns foppl.remote
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.utils :as utils]
            [foppl.hoppl :as hoppl]
            [foppl.autodiff :as autodiff]
            [foppl.eval :as eval]
            [anglican.runtime :as anglican]
            [zeromq.zmq :as zmq])

  (:import [foppl.ast constant literal-vector literal-map thunk]
           [com.google.flatbuffers FlatBufferBuilder]
           [java.nio ByteBuffer]
           [ppx Handshake HandshakeResult Message MessageBody Run RunResult
            Sample SampleResult Observe ObserveResult Forward ForwardResult
            Backward BackwardResult Distribution Uniform Normal Poisson Tensor]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  java.math alias functions     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- exp [n]
  "Alias for `Math/exp`. Since gradient functions are evaluated in the
  context of this namespace."

  (Math/exp n))

(defn- log [n]
  "Alias for `Math/log`. Since gradient functions are evaluated in the
  context of this namespace."

  (Math/log n))

(defn- sin [n]
  "Alias for `Math/sin`. Since gradient functions are evaluated in the
  context of this namespace."

  (Math/sin n))

(defn- cos [n]
  "Alias for `Math/cos`. Since gradient functions are evaluated in the
  context of this namespace."

  (Math/cos n))

;; The TCP port we will be listening to, waiting for an inference
;; engine to contact us using PPX.
(def ^:private tcp-port "5555")

;; Name of the model's language. Let's always call it FOPPL.
(def ^:private lang-name "FOPPL")

;; Name of the model being evaluated. This should ideally be set by
;; the user, but it's hardcoded for simplicity for now.
(def ^:private model-name "Remote Model")

;; maps PPX message types to constructors that, when called (without
;; arguments), return an instance of a message of that type.
(def ^:private message-type-to-class
  {MessageBody/Handshake #(Handshake.)
   MessageBody/Run #(Run.)
   MessageBody/SampleResult #(SampleResult.)
   MessageBody/ObserveResult #(ObserveResult.)
   MessageBody/Forward #(Forward.)
   MessageBody/Backward #(Backward.)})

;; Map of differentiable functions provided by this remote PPX
;; server. Ideally, these should be read from a file, but they are
;; declared statically here for demonstration purposes.
(def ^:private differentiable-function-defs
  {:exp '(fn [x] (exp x))
   :sin '(fn [x] (sin x))
   :cos '(fn [x] (cos x))
   :relu '(fn [n] (log (+ 1 (exp n))))
   :sigmoid '(fn [n] (/ 1 (+ 1 (exp (* -1 n)))))})

;; maps function names to the gradient corresponding
;; gradient-calculating functions.
(def ^:private differentiable-functions
  (let [parse #(binding [*ns* (the-ns 'foppl.remote)]
                 (eval (autodiff/perform %)))]

    (reduce (fn [m [name tree]] (assoc m name (parse tree)))
            {}
            differentiable-function-defs)))

(defn- create-zmq-socket []
  "Creates a zeromq TCP socket listening on all available interfaces
  in the port specified by the `tcp-port` constant."
  (let [context (zmq/context 1)]
    (doto (zmq/socket context :rep)
      (zmq/bind (str "tcp://*:" tcp-port)))))

(defn- receive-msg [socket types]
  "Receives a message over `socket`. Enforces that the message is of
  the one of the given `types`, throwing an exception if that is not
  the case. Returns a vector where the first element is the type of
  the message received, and the second is an instance of the message
  of the requested type."

  (let [ ;; create a `byte[]` with the data read from the socket
        blob (zmq/receive socket)

        ;; wrap it in an instance of `java.nio.ByteBuffer` (required
        ;; by FlatBuffers)
        buffer (. ByteBuffer wrap blob)

        ;; parse content as a `Message`
        message (. Message getRootAsMessage buffer)

        ;; get the message type
        message-type (.bodyType message)

        ;; get the constructor from our message-type to constructor
        ;; mapping, and create a new instance of it.
        ctor (get message-type-to-class message-type)
        obj (ctor)]

    ;; error out in case the message type is different from the valid
    ;; set of expected messages
    (when-not (some #(= message-type %) types)
      (utils/foppl-error (str "PPX: Unexpected message received (" message-type ")")))

    ;; parse the body as an instance of a message of the given type.
    [message-type (.body message obj)]))

(defn- send-msg [socket builder]
  "Convenience method to send the context of a FlatBufferBuilder over
  the network."
  (zmq/send socket (.sizedByteArray builder)))

(defn- construct-message [builder type body]
  "Given a FlatBufferBuilder and a message type and body, this will
  update the builder to include the actual message to be sent over the
  network. Adding to the buffer after this function is called will
  result in a runtime error."

  (let [offset (do
                 (. Message startMessage builder)
                 (. Message addBodyType builder type)
                 (. Message addBody builder body)
                 (. Message endMessage builder))]
    (.finish builder offset)
    offset))

(defn- matrix-map [f matrix]
  "Given a matrix and a function `f`, this eagerly applies `f` to
  every element in the matrix. Returns the resulting matrix."

  (doall (mapv #(do (mapv f %)) matrix)))

(defn- construct-sample [builder address name dist-type dist]
  "Given a FlatBufferBuilder, this will add a `Sample` table to the
  buffer with the name, address, distribution type and object
  according to the parameters passed."

  (do
    (. Sample startSample builder)
    (. Sample addAddress builder address)
    (. Sample addName builder name)
    (. Sample addDistributionType builder dist-type)
    (. Sample addDistribution builder dist)
    (. Sample endSample builder)))

(defn- construct-observe [builder address name dist-type dist value]
  "Given a FlatBufferBuilder, this will add an `Observe` table to the
  buffer using the offsets passed as arguments."

  (do
    (. Observe startObserve builder)
    (. Observe addAddress builder address)
    (. Observe addName builder name)
    (. Observe addDistributionType builder dist-type)
    (. Observe addDistribution builder dist)
    (. Observe addValue builder value)
    (. Observe endObserve builder)))

(defn- construct-run-result [builder result]
  "Given a FlatBufferBuilder, this adds a `RunResult` table to the
  buffer, to be returned to the inference engine when we are done
  running the generative model."

  (do
    (. RunResult startRunResult builder)
    (. RunResult addResult builder result)
    (. RunResult endRunResult builder)))

(defn- construct-forward-result [builder result]
  "Given a FlatBufferBuilder, this adds a `ForwardResult` table to the
  buffer, to be returned to the inference engine when forward
  computation in an automatic differentiation process is done."

  (do
    (. ForwardResult startForwardResult builder)
    (. ForwardResult addOutput builder result)
    (. ForwardResult endForwardResult builder)))

(defn- construct-backward-result [builder result]
  "Given a FlatBufferBuilder, this adds a `BackwardResult` table to
  the buffer, to be returned to the inference engine when the backward
  step in an automatic differentiation process is done."

  (do
    (. BackwardResult startBackwardResult builder)
    (. BackwardResult addGradInput builder result)
    (. BackwardResult endBackwardResult builder)))

(defn- tensor [builder data]
  "Given an array of data, this will add a `Tensor` table to the
  FlatBuffer passed. Returns the offset of the tensor in the buffer."

  (let [one-dim? (and (coll? data) (not (coll? (first data))))
        two-dim? (and (coll? data) (coll? (first data)) (not (coll? (first (first data)))))]
    (when-not (or one-dim? two-dim?)
      (utils/foppl-error "Only 1- or 2-dim tensors are supported"))

    (let [ ;; tensors are encoded as collections of doubles
          map-fn (if one-dim? mapv matrix-map)
          doubles (map-fn double data)
          reversed (doall (if one-dim? (rseq doubles) (map rseq (rseq doubles))))

          ;; we also need the shape of the tensor
          shape (if one-dim? [(count reversed)] [(count reversed) (count (first reversed))])

          ;; create the data and shape vectors into the buffer.
          data-vec (do
                     (. Tensor startDataVector builder (apply * shape))
                     (doall (map-fn #(.addDouble builder %) reversed))
                     (.endVector builder))

          shape-vec (do
                      (. Tensor startShapeVector builder (count shape))
                      (doall (map #(.addInt builder %) (reverse shape)))
                      (.endVector builder))]

      ;; finally, we can create the tensor in the flatbuffer.
      (do
        (. Tensor startTensor builder)
        (. Tensor addData builder data-vec)
        (. Tensor addShape builder shape-vec)
        (. Tensor endTensor builder)))))

(defn- tensor-to-seq [tensor]
  "Transforms a `Tensor` received from the inference engine back into
  a Clojure collection that we can manipulate. The same limitations
  described in the `tensor` function apply (i.e., only 'scalars' are
  supported)"

  (let [rows (.shape tensor 0)
        cols (.shape tensor 1)
        matrix []
        build-row (fn [i] (reduce #(conj %1 (.data tensor %2)) [] (range i (+ i cols))))]
    (reduce (fn [m curr-row] (conj m (build-row (* curr-row cols)))) matrix (range 0 rows))))

(defn- handle-handshake [socket handshake]
  "Returns this system's information back to the inference engine as a
  `HandshakeResult` message. Should be called after we received a
  handshake from the inference engine."

  (let [fbb (FlatBufferBuilder. 64)
        lang (.createString fbb lang-name)
        model (.createString fbb model-name)
        result (. HandshakeResult createHandshakeResult fbb lang model)]

    (construct-message fbb MessageBody/HandshakeResult result)
    (send-msg socket fbb)))

(defn- fill-distribution [builder dist]
  "Given a distribution object (represented as an instance of an
  Anglican distribution object), and a FlatBufferBuilder instance,
  this will insert a corresponding distribution into the
  buffer. Returns a pair of [distribution-type and
  distribution-offset]."

  (let [;; helper functions to identify the distribution being sampled
        ;; from. Assumes we are using Anglican as the underlying
        ;; library.
        uniform? #(= (class %) anglican.runtime.uniform-continuous-distribution)
        normal? #(= (class %) anglican.runtime.normal-distribution)
        poisson? #(= (class %) anglican.runtime.poisson-distribution)]

    (cond
      (uniform? dist) [Distribution/Uniform
                       (. Uniform createUniform builder (tensor builder [(:min dist)]) (tensor builder [(:max dist)]))]

      (normal? dist) [Distribution/Normal
                      (. Normal createNormal builder (tensor builder [(:mean dist)]) (tensor builder [(:sd dist)]))]

      (poisson? dist) [Distribution/Poisson
                       (. Poisson createPoisson builder (tensor builder [(:lambda dist)]))]

      :else (utils/foppl-error (str "Unsupported distribution: " (class dist))))))

(defn- request-sample [socket {dist :n} uuid env resolved pending]
  "Function called when a `sample` expression is found (during
  evaluation-based inference). Since this language is delegating all
  inference tasks to the inference engine via PPX, this function only
  sends a message to the inference engine with the distribution being
  sampled, gets a response back, and proceeds with the computation.
  Note that the `sample` AST node's UUID is used as the address of the
  corresponding random variable."

  (let [fbb (FlatBufferBuilder. 64)
        address (.createString fbb uuid)
        name (.createString fbb "")

        ;; computes the distribution type and adds the distribution
        ;; object to the flatbuffer object.
        [dist-type dist] (fill-distribution fbb dist)

        ;; construct a sample table in the flatbuffer
        sample (construct-sample fbb address name dist-type dist)]

    ;; build a `Sample` message with the data computed above --
    ;; inference engine is going to sample for us and return a result.
    (construct-message fbb MessageBody/Sample sample)
    (send-msg socket fbb)

    ;; wait for the inference engine to return a `SampleResult`. The
    ;; result should contain a tensor with the result of the sampling
    ;; process. We return the tensor as an AST constant as expected by
    ;; the evaluation module and proceed.
    (let [[_ sample-result] (receive-msg socket [MessageBody/SampleResult])
          result (.result sample-result)
          value (first (tensor-to-seq result))]

      (when-not (= (count value) 1)
        (utils/foppl-error (str "Sampled values should be scalars, got:" value)))

      [(ast/constant. (first value)) env resolved pending])))

(defn- request-observe [socket {dist :n} {val :n :as observed} uuid env resolved pending]
  "This function is called when we hit an `observe` expression while
  evaluating our model. We need to inform the inference engine about
  the random variable being observed, and what value was observed. On
  success, the inference engine sends a (empty) `ObserveResult`
  message. Evaluating this function returns the observed value,
  although this is not relevant for this remote inference scenario."

  (let [fbb (FlatBufferBuilder. 64)
        address (.createString fbb uuid)
        name (.createString fbb "")

        [dist-type dist] (fill-distribution fbb dist)
        observed (tensor fbb [val])
        observe (construct-observe fbb address name dist-type dist observed)]

    (construct-message fbb MessageBody/Observe observe)
    (send-msg socket fbb)

    (receive-msg socket [MessageBody/ObserveResult])
    [observed env resolved pending]))

(defn- run-result [socket val]
  "Returns a result `val` of evaluating the generative model. Sends a
  `RunResult` message to the inference engine. After this is sent, the
  model server is supposed to wait for another `Run` message, should
  the inference engine desire to run the model more times in order to
  determine a posterior distribution."

  (when (seq? val)
    (utils/foppl-error "Multidimensional results not supported."))

  (let [fbb (FlatBufferBuilder. 64)
        result (tensor fbb [val])
        rr (construct-run-result fbb result)]

    (construct-message fbb MessageBody/RunResult rr)
    (send-msg socket fbb)))

(defn- autograd-apply [name args]
  "Calculates the gradient of a function with the given `name` with
  the given `args`. If the function is not declared in
  `differentiable-functions`, this will throw an exception. Returns a
  vector of the form `[function-result, gradient-wrt-each-parameter]`"

  (let [grad-fn (doto (get differentiable-functions (keyword name))
                  (when-not
                      (utils/foppl-error (str "Unknown differentiable function: " name))))]

    (apply grad-fn [args])))

(defn- element-wise [f m1 m2]
  "Given two matrices `m1` and `m2` of the exact same dimensions, this
  applies a function `f` that takes two arguments to every pair of
  elements in the matrices. Returns the resulting matrix."

  ;; make sure the two matrices are of the same size.
  (when-not (and (= (count m1) (count m2)) (= (count (first m1)) (count (first m2))))
    (utils/foppl-error "Element-wise operations are only applicable in matrices of the same shape."))

  (let [rows (count m1)

        ;; given a row (index), this returns a vector where `f` has
        ;; been applied on the that row in the two matrices.
        combine-row #(conj %1 (mapv f (nth m1 %2) (nth m2 %2)))]

    (reduce combine-row [] (range 0 rows))))

(defn- autograd-forward [socket name args]
  "Handles the forward passs in an automatic differentiation process."

  (let [forwards (matrix-map (comp first (partial autograd-apply name)) args)
        fbb (FlatBufferBuilder. 64)
        result (tensor fbb forwards)
        fr (construct-forward-result fbb result)]

    (construct-message fbb MessageBody/ForwardResult fr)
    (send-msg socket fbb)))

(defn- autograd-backward [socket name args grad-output]
  "Handles the backward pass in an automatic differentiation process."

  (let [backwards (matrix-map (comp first vals last (partial autograd-apply name)) args)
        fbb (FlatBufferBuilder. 64)
        result (element-wise * backwards grad-output)
        output (tensor fbb result)
        br (construct-backward-result fbb output)]

    (construct-message fbb MessageBody/BackwardResult br)
    (send-msg socket fbb)))

;; `lazy-evaluation-visitor` lazily evaluates `sample` and `observe`
;; expressions and batches operations at strict points (control flow
;; and termination).
(defrecord lazy-evaluation-visitor [rho env resolved pending sample-fn observe-fn])

(defn- with-env [new-vars {rho :rho env :env resolved :resolved pending :pending sample-fn :sample-fn observe-fn :observe-fn}]
  "Extends the execution environment with `new-vars`, a map from
  variable name to values (constant AST nodes)."

  (lazy-evaluation-visitor. rho (merge env new-vars) resolved pending sample-fn observe-fn))

(defn- with-resolved [new-resolved {rho :rho env :env resolved :resolved pending :pending sample-fn :sample-fn observe-fn :observe-fn}]
  "Extends the execution environment with `new-resolved`, a map from
  thunk identifiers to values."

  (lazy-evaluation-visitor. rho env (merge resolved new-resolved) pending sample-fn observe-fn))

(defn- with-pending [new-pending {rho :rho env :env resolved :resolved pending :pending sample-fn :sample-fn observe-fn :observe-fn}]
  "Extends the execution environment with `new-pending`, a vector of
  thunks to be executed later.."

  (lazy-evaluation-visitor. rho env resolved new-pending sample-fn observe-fn))

(defn- eval-coll [es {env :env resolved :resolved pending :pending :as v}]
  (let [visit-expression (fn [[es-coll current-env current-resolved current-pending] e]
                           (let [visitor (->> v
                                              (with-env current-env)
                                              (with-resolved current-resolved)
                                              (with-pending current-pending))
                                 [reduced-e new-env new-resolved new-pending] (accept e visitor)]
                             [(conj es-coll reduced-e) new-env new-resolved new-pending]))]
    (reduce visit-expression [[] env resolved pending] es)))

(extend-type lazy-evaluation-visitor
  ast/visitor

  (visit-constant [{env :env resolved :resolved pending :pending} c]
    [c env resolved pending])

  (visit-variable [{env :env resolved :resolved pending :pending} {name :name}]
    ;; only variables contained in the evaluation environment are
    ;; defined.  Referencing any other variable is an error indicating
    ;; that the user attempted to use an undefined/unbound variable.
    (when-not (contains? env name)
      (utils/foppl-error (str "Error: Undefined variable: " name)))

    [(get env name) env resolved pending])

  (visit-literal-vector [v {es :es}]
    (let [[reduced-es new-env new-resolved new-pending] (eval-coll es v)]
      [(ast/literal-vector. reduced-es) new-env new-resolved new-pending]))

  (visit-literal-map [v {es :es}]
    (let [[reduced-es new-env new-resolved new-pending] (eval-coll es v)]
      [(ast/literal-map. reduced-es) new-env new-resolved new-pending]))

  (visit-procedure [v {name :name args :args e :e}]
    (utils/foppl-error "Procedure definitions should not exist during evaluation-based inference"))

  (visit-lambda [{env :env resolved :resolved pending :pending} lambda]
    [lambda env resolved pending])

  (visit-local-binding [v {bindings :bindings es :es}]
    {:pre [(= (count bindings) 2) (= (count es) 1)]}

    (let [ ;; find the name of the variable being bound, as well as the
          ;; value.
          bound-name (:name (first bindings))
          bound-val (second bindings)

          ;; reduce the bound value
          [c1 new-env new-resolved new-pending] (accept bound-val v)

          ;; extend the environment to bind the name to the reduced
          ;; value
          env-extension {bound-name c1}
          e (first es)

          visitor (->> v
                       (with-env env-extension)
                       (with-resolved new-resolved)
                       (with-pending new-pending))]

      (accept e visitor)))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (utils/foppl-error "foreach expressions are not valid in HOPPL"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (utils/foppl-error "loop expressions should have been desugared during evaluation-based inference"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [[reduced-predicate new-env new-resolved new-pending] (accept predicate v)
          visitor (->> v
                       (with-env new-env)
                       (with-resolved new-resolved)
                       (with-pending new-pending))]
      (if (hoppl/to-clojure-value reduced-predicate)
        (accept then visitor)
        (accept else visitor))))

  (visit-fn-application [{rho :rho env :env store :store :as v} {name :name args :args}]
    (let [[reduced-args new-env new-resolved new-pending] (eval-coll args v)
          clojure-args (map hoppl/to-clojure-value reduced-args)
          builtin? #(contains? eval/all-builtins %)
          visitor (->> v
                       (with-env new-env)
                       (with-resolved new-resolved)
                       (with-pending new-pending))]

      (cond
        ;; if the function being applied is a user-defined procedure
        ;; (or a builtin higher order function), we extend the
        ;; environment with the function parameters being bound to the
        ;; arguments passed, and recursively evaluate the expression
        ;; contained in the procedure definition
        (contains? rho name) (let [[param-names e] (get rho name)
                                   env-extension (zipmap param-names reduced-args)]
                               (accept e (with-env env-extension visitor)))

        ;; in case the function being applied is a built-in,
        ;; first-order function, we immediately apply it with the
        ;; arguments given. The result should be a constant value.
        (builtin? name) [(ast/constant. (apply (eval/builtin-fn name) clojure-args)) new-env new-resolved new-pending]

        ;; if the function being applied is in the evaluation context,
        ;; it means it was defined as a lambda previously (no
        ;; type-checking to ensure this is actually the case is
        ;; performed).
        ;;
        ;; This case is similar to the user-defined procedure
        ;; scenario. The value associated with the name in the
        ;; evaluation environment is treated as a lambda AST node, the
        ;; environment is extended with the lambda parameters being
        ;; bound to the arguments passed, and the expression
        ;; associated with the lambda is recursively evaluated.
        (contains? env name) (let [{name :name params :args e :e} (get env name)
                                   params-names (map :name params)
                                   env-extension (zipmap params-names reduced-args)]
                               (accept e (with-env env-extension visitor)))

        :else (utils/foppl-error (str "Undefined function: " name)))))

  (visit-sample [{sample-fn :sample-fn :as v} {dist :dist uuid :uuid}]
    ;; behavior is inference-algorithm specific. Invoke the
    ;; `sample-fn` function passed to the visitor.
    (let [[reduced-dist new-env new-resolved new-pending] (accept dist v)]
      (sample-fn reduced-dist uuid new-env new-resolved new-pending)))

  (visit-observe [{observe-fn :observe-fn :as v} {dist :dist val :val uuid :uuid}]
    ;; behavior is inference-algorithm specific. Invoke the
    ;; `observe-fn` function passed to the visitor.
    (let [[reduced-dist env' resolved' pending'] (accept dist v)
          val-visitor (->> v
                           (with-env env')
                           (with-resolved resolved')
                           (with-pending pending'))
          [reduced-val new-env new-resolved new-pending] (accept val val-visitor)]
      (observe-fn reduced-dist reduced-val uuid new-env new-resolved new-pending))))

(defn- lazy-sample [{dist :n} {val :n} uuid env resolved pending]
  (ast/thunk. (ast/fresh-sym "thunk-sample") :sample [dist val uuid]))

(defn- lazy-observe [{dist :n} {val :n} uuid env resolved pending])

(defn- lazy-interpret [sample-fn observe-fn {defs :defs e :e}]
  (let [;; procedure names of user-defined functions and higher-order
        ;; builtins
        procedure-names (map :name defs)
        procedure-args (fn [{args :args}] (map :name args))
        encode-procedure (fn [procedure] [(into [] (procedure-args procedure)) (:e procedure)])
        encoded (map encode-procedure defs)

        ;; the rho map is a map from procedure name to a tuple
        ;; (vector) containing [list-of-variable-names expression]
        rho (zipmap procedure-names encoded)

        ;; the evaluation environment initially starts empty
        env {}

        ;; at first, no pending expressions have been resolved
        resolved {}

        ;; at first, no expression is pending
        pending []

        v (lazy-evaluation-visitor. rho env resolved pending sample-fn observe-fn)]
    (accept e v)))


(defn perform
  "Performs waits for communication from some inference engine that
  implements the PPX protocol and controls the generative model
  specified by the `program` passed as parameter."

  ;; if no `logger` was passed, use `println` to log messages to
  ;; standard output
  ([program] (perform program println))

  ([program logger]
   (with-open [socket (create-zmq-socket)]
     (logger (str "Listening on tcp://*:" tcp-port))
     (logger "Waiting for handshake from inference engine.")

     (let [ ;; before the model is run, the inference engine needs to
           ;; send a handshake message to initiate communication.
           [_ handshake] (receive-msg socket [MessageBody/Handshake])

           ;; the handshake needs to be followed by a
           ;; `HandshakeResult`, in which the language and model
           ;; names are communicated.
           _ (handle-handshake socket handshake)

           ;; get the system (inference engine's) name from the
           ;; handshake message received
           system-name (.systemName handshake)]

       (logger "Got handshake from" system-name)

       ;; infinite loop where we wait for the next message from the
       ;; inference engine. It must be either a `Run` operation, in
       ;; which case the generative model is run and the result is
       ;; returned back to the inference engine; or a `Forward` call,
       ;; indicating that the inference engine is performing automatic
       ;; differentiation of a function that is partly defined here.
       ;; (by taking one element from the lazy sequence), return the
       ;; result back to the inference engine, and recur.
       (let [sample-fn (partial request-sample socket)
             observe-fn (partial request-observe socket)
             eager-interpreter (partial lazy-interpret sample-fn observe-fn)
             lazy-interpreter (partial lazy-interpret lazy-sample lazy-observe)
             next-msg #(receive-msg socket [MessageBody/Run MessageBody/Forward MessageBody/Backward])]
         (loop [[type message] (next-msg)]
           (cond
             (= type MessageBody/Run) (do
                                        (logger "Running the model")

                                        (let [[{val :n} *] (hoppl/forward program eager-interpreter)]
                                          (run-result socket val)))

             (= type MessageBody/Forward) (do
                                            (logger "Calculating" (.name message) "gradient (forward)")
                                            (autograd-forward socket (.name message) (tensor-to-seq (.input message))))

             (= type MessageBody/Backward) (do
                                             (logger "Calculating" (.name message) "gradient (backward)")
                                             (autograd-backward socket
                                                                (.name message)
                                                                (tensor-to-seq (.input message))
                                                                (tensor-to-seq (.gradOutput message)))))


           (recur (next-msg))))))))
