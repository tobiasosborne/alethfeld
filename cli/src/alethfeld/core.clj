(ns alethfeld.core
  "Main entry point for Alethfeld CLI v0.1.0."
  (:require [alethfeld.version :as version]
            [clojure.tools.cli :refer [parse-opts]])
  (:gen-class))

(def cli-options
  [["-h" "--help" "Show help"]
   ["-V" "--version" "Show version"]])

(defn -main [& args]
  (let [{:keys [options arguments errors summary]} (parse-opts args cli-options)]
    (cond
      (:help options)
      (do
        (println (version/version-string))
        (println)
        (println "Usage: alethfeld <command> [options]")
        (println)
        (println "Commands:")
        (println "  context       Emit phase-specific prompt fragment")
        (println "  next          Suggest optimal next action")
        (println "  help          Show command help")
        (println "  schema        Show EDN schemas")
        (println "  fsm           Workflow state machine operations")
        (println "  init          Initialize a new proof graph")
        (println "  add-node      Add a node to the graph")
        (println "  update-status Update node verification status")
        (println "  validate      Validate graph integrity")
        (println "  stats         Show graph statistics")
        (println "  ... (more commands in development)")
        (println)
        (println "Global options:")
        (println summary)
        (System/exit 0))

      (:version options)
      (do
        (println (version/version-string))
        (System/exit 0))

      :else
      (do
        (println (str "Alethfeld CLI v" version/version " - commands not yet implemented"))
        (println "Run with --help for usage information.")
        (System/exit 1)))))
