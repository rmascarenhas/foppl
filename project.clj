(defproject foppl "0.1.0-SNAPSHOT"
  :description "FOPPL: A First-Order Probabilistic Programming Language"
  :url "https://www.cs.ubc.ca/~fwood/CS532W-539W/homework/4.html"
  :license {:name "MIT"
            :url "https://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [anglican "1.0.0"]]
  :main ^:skip-aot foppl.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})
