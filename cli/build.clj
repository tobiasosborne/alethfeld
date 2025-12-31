(ns build
  (:require [clojure.tools.build.api :as b]))

(def lib 'com.github.tobiasosborne/alethfeld)
(def version "0.1.0")
(def class-dir "target/classes")
(def basis (b/create-basis {:project "deps.edn"}))
(def jar-file (format "target/alethfeld-%s.jar" version))
(def uber-file "target/alethfeld.jar")

(defn clean [_]
  "Remove build artifacts."
  (b/delete {:path "target"}))

(defn jar [_]
  "Build a standard JAR."
  (b/write-pom {:class-dir class-dir
                :lib lib
                :version version
                :basis basis
                :src-dirs ["src"]})
  (b/copy-dir {:src-dirs ["src" "resources"]
               :target-dir class-dir})
  (b/jar {:class-dir class-dir
          :jar-file jar-file}))

(defn uber [_]
  "Build an uberjar (all dependencies included)."
  (clean nil)
  (b/copy-dir {:src-dirs ["src" "resources"]
               :target-dir class-dir})
  (b/compile-clj {:basis basis
                  :class-dir class-dir
                  :src-dirs ["src"]})
  (b/uber {:class-dir class-dir
           :uber-file uber-file
           :basis basis
           :main 'alethfeld.core})
  (println (str "✓ Uberjar created: " uber-file)))
