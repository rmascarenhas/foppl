(defproject foppl "0.1.0-SNAPSHOT"
  :description "FOPPL: A First-Order Probabilistic Programming Language"
  :url "https://www.cs.ubc.ca/~fwood/CS532W-539W/homework/4.html"
  :license {:name "MIT"
            :url "https://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [anglican "1.0.0"]
                 [com.google.flatbuffers/flatbuffers-java "1.10.0"]
                 [org.zeromq/jeromq "0.4.3"]
                 [org.zeromq/cljzmq "0.1.4" :exclusions [org.zeromq/jzmq]]]
  :main ^:skip-aot foppl.core
  :java-source-paths ["src/java/ppx"]
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})
