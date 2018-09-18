(ns foppl.utils
  "Utility functions"
  )

(defn- runtime-error [& {:keys [type message]}]
  (throw (ex-info message {:type type})))

(defn ice [msg]
  "Throws an exception that is reported to the end user as an
  internal compiler error. Should only be used in situations
  deemed 'unreachable' and irrecoverable"
  (runtime-error :type :ice :message msg))

(defn foppl-error [msg]
  "Throws an exception that is reported to the end user as an
  invalid FOPPL program. This error should be used when validating
  the semantics of programs given to the compiler."
  (runtime-error :type :invalid-program :message msg))
