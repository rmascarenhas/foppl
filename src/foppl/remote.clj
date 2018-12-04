(ns foppl.remote
  (:require [foppl.ast :as ast]
            [foppl.utils :as utils]
            [foppl.hoppl :as hoppl]
            [anglican.runtime :as anglican]
            [zeromq.zmq :as zmq])

  (:import [foppl.ast constant]
           [com.google.flatbuffers FlatBufferBuilder]
           [java.nio ByteBuffer]
           [ppx Handshake HandshakeResult Message MessageBody]))

(def ^:private tcp-port "5032")

(def ^:private lang-name "FOPPL")

(def ^:private model-name "Remote Model")

(defn- create-zmq-socket []
  (let [context (zmq/context 1)]
    (doto (zmq/socket context :rep)
      (zmq/bind (str "tcp://*:" tcp-port)))))

(defn- handshake [socket]
  (let [bytes (zmq/receive socket)
        buffer (. ByteBuffer wrap bytes)
        message (. Message getRootAsMessage buffer)
        type (.bodyType message)]

    (when-not (= type MessageBody/Handshake)
      (utils/foppl-error (str "PPX: Expected handshake message, got: " type)))

    (let [handshake (.body message (Handshake.))
          system-name (.systemName handshake)
          fbb (FlatBufferBuilder. 64)
          lang-offset (.createString fbb lang-name)
          model-offset (.createString fbb model-name)]

      (. HandshakeResult createHandshakeResult fbb lang-offset model-offset)
      (.finish fbb)
      (zmq/send socket (.dataBuffer fbb))
      system-name)))

(defn- init-store []
  {})

(defn- request-sample [{dist :n} store]
  [(ast/constant. (anglican/sample* dist)) store])

(defn- request-observe [{dist :n} {val :n :as observed} store]
  (let [log-prob (anglican/observe* dist val)]
    [observed store]))

;; flow:
;;     1. listen on zmq socket
;;     2. wait for handshake
;;     3. on handshake, enter state machine:
;;         a. wait for Run
;;         b. (take 1) from lazy seq
;;         c. Return Result above, loop
(defn perform
  ([program] (perform program println))

  ([program logger]
   (let [samples (hoppl/perform program init-store request-sample request-observe)]
     (with-open [socket (create-zmq-socket)]
       (logger (str "Listening on tcp://*:" tcp-port))
       (logger "Waiting for handshake from inference engine.")

       (loop []
         (logger "Got handshake from " (handshake socket))
         (recur))))))

