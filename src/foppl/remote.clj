(ns foppl.remote
  (:require [foppl.ast :as ast]
            [foppl.utils :as utils]
            [foppl.hoppl :as hoppl]
            [anglican.runtime :as anglican]
            [zeromq.zmq :as zmq])

  (:import [foppl.ast constant]
           [com.google.flatbuffers FlatBufferBuilder]
           [java.nio ByteBuffer]
           [ppx Handshake HandshakeResult Message MessageBody Run RunResult]))

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
   MessageBody/Run #(Run.)})

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

  (let [;; create a `byte[]` with the data read from the socket
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

(defn- handle-handshake [socket handshake]
  "Returns this system's information back to the inference engine as a
  `HandshakeResult` message. Should be called after we received a
  handshake from the inference engine."

  (let [fbb (FlatBufferBuilder. 64)
        lang-offset (.createString fbb lang-name)
        model-offset (.createString fbb model-name)
        result-offset (. HandshakeResult createHandshakeResult fbb lang-offset model-offset)
        buffer-size (do
                      (. Message startMessage fbb)
                      (. Message addBodyType fbb MessageBody/HandshakeResult)
                      (. Message addBody fbb result-offset)
                      (. Message endMessage fbb))]

    (.finish fbb buffer-size)
    (zmq/send socket (.sizedByteArray fbb))))

(defn- init-store []
  ;; a store is not used when doing evaluation-based inference in this
  ;; remote model, so just return an empty map.
  {})

(defn- request-sample [socket {dist :n} store]
  [(ast/constant. (anglican/sample* dist)) store])

(defn- request-observe [socket {dist :n} {val :n :as observed} store]
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
         samples-lazy-seq #(hoppl/perform program init-store (partial request-sample %) (partial request-observe %))]

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
             system-name (.systemName handshake)

             ;; we are now able to build our lazy sequence of samples
             ;; since we are connected to the inference engine.
             samples (samples-lazy-seq socket)]

         (logger "Got handshake from" system-name)

         ;; we just need to wait for a `Run` message to be received,
         ;; in which case we sample from the generative model (by
         ;; taking one element from the lazy sequence), and recur.
         (loop []
           (receive-msg socket MessageBody/Run)
           (take 1 samples)
           (recur)))))))

