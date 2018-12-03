(ns foppl.remote
  (:require [foppl.hoppl :as hoppl])
  (:import [ppx Handshake HandshakeResult]))

(defn- init-server)

(defn- request-sample [dist store])

(defn- request-observe [dist val store])

(defn perform [program]
  (hoppl/perform program init-server request-sample request-observe))
