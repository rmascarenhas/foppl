(ns foppl.remote
  (:require [foppl.ast :as ast]
            [foppl.utils :as utils]
            [foppl.hoppl :as hoppl]
            [anglican.runtime :as anglican]
            [zeromq.zmq :as zmq])

  (:import [foppl.ast constant]
           [com.google.flatbuffers FlatBufferBuilder]
           [java.nio ByteBuffer]
           [ppx Handshake HandshakeResult Message MessageBody Run RunResult
            Sample SampleResult Observe ObserveResult Distribution
            Uniform Normal Tensor]))

;; The TCP port we will be listening to, waiting for an inference
;; engine to contact us using PPX.
(def ^:private tcp-port "5032")

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
   MessageBody/SampleResult #(SampleResult.)})

(defn- create-zmq-socket []
  "Creates a zeromq TCP socket listening on all available interfaces
  in the port specified by the `tcp-port` constant."
  (let [context (zmq/context 1)]
    (doto (zmq/socket context :rep)
      (zmq/bind (str "tcp://*:" tcp-port)))))

(defn- receive-msg [socket type]
  "Receives a message over `socket`. Enforces that the message is of
  the given `type`, throwing an exception if that is not the
  case. Returns an instace of the message of the requested type."

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
        ctor (get message-type-to-class type)
        obj (ctor)]

    ;; error out in case the message type is different from the one
    ;; expected.
    (when-not (= type message-type)
      (utils/foppl-error (str "PPX: Unexpected message received (" message-type ")")))

    ;; parse the body as an instance of a message of the given type.
    (.body message obj)))

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

(defn- tensor [builder array]
  "Given an array of data, this will add a `Tensor` table to the
  FlatBuffer passed. Returns the offset of the tensor in the buffer."

  (let [;; tensors are encoded as collections of doubles
        doubles (map double array)

        ;; we also need the shape of the tensor
        shape [(count doubles)]

        ;; create the data and shape vectors into the buffer.
        data-vec (. Tensor createDataVector builder (double-array doubles))
        shape-vec (. Tensor createShapeVector builder (int-array shape))]

    ;; for simplicity (and since most of the simple distributions we
    ;; are concerned with do not need them), we will only support
    ;; "scalars" as tensors.
    (when-not (= (count doubles) 1)
      (utils/foppl-error "Multidimensional tensors not supported."))

    ;; finally, we can create the tensor in the flatbuffer.
    (do
      (. Tensor startTensor builder)
      (. Tensor addData builder data-vec)
      (. Tensor addShape builder shape-vec)
      (. Tensor endTensor builder))))

(defn- tensor-to-seq [tensor]
  "Transforms a `Tensor` received from the inference engine back into
  a Clojure collection that we can manipulate. The same limitations
  described in the `tensor` function apply (i.e., only 'scalars' are
  supported)"

  (when-not (= (.shapeLength tensor) 1)
    (utils/foppl-error "Multidimensional tensors not supported."))

  (let [shape (.shape tensor 0)]
    (reduce #(conj %1 (.data tensor %2)) [] (range 0 shape))))

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

(defn- init-store []
  ;; a store is not used when doing evaluation-based inference in this
  ;; remote model, so just return an empty map.
  {})

(defn- request-sample [socket {dist :n} store uuid]
  "Function called when a `sample` expression is found (during
  evaluation-based inference). Since this language is delegating all
  inference tasks to the inference engine via PPX, this function only
  sends a message to the inference engine with the distribution being
  sampled, gets a response back, and proceeds with the
  computation. Note that the `sample` AST node's UUID is used as the
  address of the corresponding random variable."

  (let [;; helper functions to identify the distribution being sampled
        ;; from. Assumes we are using Anglican as the underlying
        ;; library.
        uniform? #(= (class %) anglican.runtime.uniform-continuous-distribution)
        normal? #(= (class %) anglican.runtime.normal-distribution)

        fbb (FlatBufferBuilder. 64)
        address (.createString fbb uuid)
        name (.createString fbb "")

        ;; we need to fill the `distribution` union on `Sample` with
        ;; the correct distribution type; this checks the type of
        ;; distribution being sampled and computes the distribution
        ;; type and adds the distribution object to the flatbuffer
        ;; object correspondingly.
        [dist-type dist] (cond
                           (uniform? dist) [Distribution/Uniform
                                            (. Uniform createUniform fbb (tensor fbb [(:min dist)]) (tensor fbb [(:max dist)]))]

                           (normal? dist) [Distribution/Normal
                                           (. Normal createNormal fbb (tensor fbb [(:mean dist)]) (tensor fbb [(:sd dist)]))]

                           :else (utils/foppl-error (str "Unsupported distribution: " (class dist))))

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
    (let [sample-result (receive-msg socket MessageBody/SampleResult)
          result (.result sample-result)
          value (tensor-to-seq result)]

      (when-not (= (count value) 1)
        (utils/foppl-error (str "Sampled values should be scalars, got:" value)))

      [(ast/constant. (first value)) store])))

(defn- request-observe [socket {dist :n} {val :n :as observed} store uuid]
  (let [log-prob (anglican/observe* dist val)]
    [observed store]))

(defn perform
  "Performs waits for communication from some inference engine that
  implements the PPX protocol and controls the generative model
  specified by the `program` passed as parameter."

  ;; if no `logger` was passed, use `println` to log messages to
  ;; standard output
  ([program] (perform program println))

  ([program logger]
   (let [;; given a socket, this will return a lazy sequence of
         ;; samples from the generative model. The socket is necessary
         ;; since sample and observe expressions need to contact the
         ;; inference engine in order to register random variables and
         ;; get samples and log probabilities.
         build-lazy-seq #(hoppl/perform program init-store (partial request-sample %) (partial request-observe %))]

     (with-open [socket (create-zmq-socket)]
       (logger (str "Listening on tcp://*:" tcp-port))
       (logger "Waiting for handshake from inference engine.")

       (let [;; before the model is run, the inference engine needs to
             ;; send a handshake message to initiate communication.
             handshake (receive-msg socket MessageBody/Handshake)

             ;; the handshake needs to be followed by a
             ;; `HandshakeResult`, in which the language and model
             ;; names are communicated.
             _ (handle-handshake socket handshake)

             ;; get the system (inference engine's) name from the
             ;; handshake message received
             system-name (.systemName handshake)]

         (logger "Got handshake from" system-name)

         ;; once the handshake was received from the inference engine,
         ;; we now wait for it to instruct the generative model to
         ;; `Run`.
         (receive-msg socket MessageBody/Run)

         ;; infinite loop where we sample from the generative model
         ;; (by taking one element from the lazy sequence), return the
         ;; result back to the inference engine, and recur.
         (let [samples (build-lazy-seq socket)]
           (loop []
             (let [[val _] (take 1 samples)]
               ;; (run-result val) return the result to the inference engine
               (receive-msg socket MessageBody/Run)
               (recur)))))))))
