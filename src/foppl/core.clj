(ns foppl.core
  "Defines the compiler's main function. Validates command line parameters and
  gets the compilation pipeline started."
  (:require [clojure.string :as string]
            [clojure.java.io :as io]
            [foppl.ast :as ast]
            [foppl.validation :as validation]
            [foppl.scope :as scope]
            [foppl.desugar :as desugar]
            [foppl.graphical :as graphical]
            [foppl.sampling :as sampling]
            [foppl.hoppl :as hoppl]
            [foppl.formatter :as formatter])
  (:gen-class))

(def ^:private me "foppl")

(def ^:private help-msg
  (string/join "\n" [(str "Usage: " me " [source]")
                     (str "[source] is the path to a file. When - is used, " me " will read from STDIN")]))

(defn- error [msg]
  "Prints the error message given and the help message to STDERR.
  Terminates execution with an unsuccessful exit status."
  (binding [*out* *err*]
    (println (str "ERROR: " msg))
    (println)
    (println help-msg)
    (System/exit 1)))

(defn -main
  "Compiler's entrypoint.
  Reads the file given (or from standard input if no argument is
  passed on the command line) and produces a Clojure data structure
  representing a graphical model corresponding to the program given."
  [& args]

  ;; only one command line parameter is expected. If more than one is
  ;; passed, the user does not know how to use FOPPL. Print a help
  ;; message and terminate
  (when-not (= (count args) 1)
    (error "Wrong number of arguments"))

  ;; if not reading from STDIN, make sure that the path given on
  ;; the command line actually exists as a file on the user's
  ;; filesystem
  (let [src (first args)]
    (when-not (= src "-p")
      (when-not (.exists (io/as-file src))
        (error (str "File not found: " src)))))

  ;; creates the PushbackReader object required by ast/read-source
  ;; and sets up the compilation pipeline
  (let [[path] args
        fd (if (= path "-") *in*  (io/reader path))
        stream (java.io.PushbackReader. fd)]
    (try
      (->> stream
           ast/read-source
           validation/perform
           hoppl/perform
           (take 10)
           println)
      (catch clojure.lang.ExceptionInfo e
        (let [type (-> e ex-data :type)
              msg (-> (.getMessage e))]
          (cond
            (= type :ice) (error (str "Internal Compiler Error: " msg))
            (= type :invalid-program) (error (str "Invalid FOPPL program: " msg))
            :else (error (str "Unhandled exception: " msg)))))
      (catch RuntimeException e (error (str "Syntax error: " (.getMessage e))))
      (catch AssertionError e (error (str "Invariant violated: " (.getMessage e))))))
  )
