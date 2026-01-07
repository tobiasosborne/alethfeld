(ns alethfeld.version
  "Version information for Alethfeld CLI.")

(def version "0.1.0")

(def spec-version "2.3")

(def version-info
  {:version version
   :spec-version spec-version
   :name "Alethfeld CLI"
   :description "Semantic proof graph operations with context emission"})

(defn version-string []
  (str "Alethfeld CLI v" version " (spec v" spec-version ")"))
