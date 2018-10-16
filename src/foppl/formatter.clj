(ns foppl.formatter
  "Formats the AST back into a textual representation."
  (:require [foppl.ast :as ast :refer [accept]]
            [foppl.utils :as utils]
            [clojure.string :as s])
  (:import [foppl.ast fn-application definition local-binding if-cond sample observe program]))

;; The formattter visitor traverses the AST and produces a textual representation of
;; the parsed code. Note that minimum effort was put into producing nicely formatted
;; output. In general, this formatter is intended to be used only for "small" S-expressions,
;; such as those most often needed when compiling the target graphical models.
(defrecord formatter-visitor [])

(defn- accept-coll
  "Visits a collection of AST nodes in sequence, and joins the serialized
  representation of each node using the separator given (or a white-space
  character when no separator was passed.)"
  ([coll v] (accept-coll " " coll v))
  ([sep coll v]
   (let [format (fn [n] (accept n v))]
     (s/join sep (map format coll)))))

(extend-type formatter-visitor
  ast/visitor

  (visit-constant [_ {c :n}]
    (cond
      (string? c) (str "\"" c "\"")
      (symbol? c) (str "'" c)
      :else (str c)))

  (visit-variable [_ {name :name}]
    (str name))

  (visit-literal-vector [v {es :es}]
    (str "[" (accept-coll es v) "]"))

  (visit-literal-map [v {es :es}]
    (str "{" (accept-coll es v) "}"))

  (visit-definition [v {name :name args :args e :e}]
    (if name
      (str "(defn " name " [" (accept-coll args v) "] " (accept e v) ")")
      (str "(fn [" (accept-coll args v) "] " (accept e v) ")")))

  (visit-local-binding [v {bindings :bindings es :es}]
    (str "(let [" (accept-coll bindings v) "] " (accept-coll es v) ")"))

  (visit-foreach [v {c :c bindings :bindings es :es}]
    (str "(foreach " (accept c v) " [" (accept-coll bindings v) "]" (accept-coll "\n" es v) ")"))

  (visit-loop [v {c :c e :e f :f es :es}]
    (str "(loop " (accept c v) " " (accept e v) " " (accept f v) " " (accept-coll es v) ")"))

  (visit-if-cond [v {predicate :predicate then :then else :else}]
    (let [else-str (accept else v)
          then-else-sep (if (empty? else-str) "" " ")]
      (str "(if " (accept predicate v) " " (accept then v) then-else-sep (accept else v) ")")))

  (visit-fn-application [v {name :name args :args}]
    (str "(" name (if (empty? args) "" " ") (accept-coll args v) ")"))

  (visit-sample [v {dist :dist}]
    (str "(sample " (accept dist v) ")"))

  (visit-observe [v {dist :dist val :val}]
    (str "(observe " (accept dist v) " " (accept val v) ")"))
  )

(defn to-str [n]
  "Given an AST node, this function returns its string representation."
  (let [v (formatter-visitor.)]
    (accept n v)))

(defn perform [{defs :defs e :e}]
  "Performs serialization of the AST into a textual representation.
  Returns a string."
  (let [visitor (formatter-visitor.)
        format (fn [n]  (accept n visitor))]
    (s/join "\n" (conj (mapv format defs) (format e)))))
