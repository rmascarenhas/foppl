(ns foppl.utils
  "Utility functions"
  )

(defn- runtime-error [& {:keys [type message]}]
  (throw (ex-info message {:type type})))

(defn ice [msg]
  (runtime-error :type :ice :message msg))

(defn foppl-error [msg]
  (runtime-error :type :invalid-program :message msg))
