(ns foppl.utils
  "Utility functions"
  )

(defn- runtime-error [& msgs]
  (throw (RuntimeException. (apply str msgs))))

(defn ice [msg]
  (runtime-error "Internal Compiler Error: " msg))

(defn foppl-error [msg]
  (runtime-error "Invalid FOPPL program: " msg))
