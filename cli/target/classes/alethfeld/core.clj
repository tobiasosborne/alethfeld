(ns alethfeld.core
  "CLI entry point for Alethfeld semantic proof graph operations."
  (:require [clojure.tools.cli :refer [parse-opts]]
            [clojure.string :as str]
            [alethfeld.commands.validate :as validate]
            [alethfeld.commands.add-node :as add-node]
            [alethfeld.commands.update-status :as update-status]
            [alethfeld.commands.delete-node :as delete-node]
            [alethfeld.commands.replace-node :as replace-node]
            [alethfeld.commands.external-ref :as external-ref]
            [alethfeld.commands.extract-lemma :as extract-lemma]
            [alethfeld.commands.init :as init]
            [alethfeld.commands.stats :as stats]
            [alethfeld.commands.recompute :as recompute]
            [alethfeld.commands.convert :as convert])
  (:gen-class))

;; =============================================================================
;; Command Registry
;; =============================================================================

(def commands
  {"validate" {:fn validate/run
               :desc "Validate a semantic proof graph EDN file"
               :options validate/cli-options}
   "add-node" {:fn add-node/run
               :desc "Add a node to a graph"
               :options add-node/cli-options}
   "update-status" {:fn update-status/run
                    :desc "Update node verification status"
                    :options update-status/cli-options}
   "delete-node" {:fn delete-node/run
                  :desc "Delete (archive) a node from a graph"
                  :options delete-node/cli-options}
   "replace-node" {:fn replace-node/run
                   :desc "Replace a rejected node with revised version"
                   :options replace-node/cli-options}
   "external-ref" {:fn external-ref/run
                   :desc "Manage external references (citations)"
                   :options external-ref/cli-options}
   "extract-lemma" {:fn extract-lemma/run
                    :desc "Extract verified subgraph as independent lemma"
                    :options extract-lemma/cli-options}
   "init" {:fn init/run
           :desc "Initialize a new semantic proof graph"
           :options init/cli-options}
   "stats" {:fn stats/run
            :desc "Display graph statistics"
            :options stats/cli-options}
   "recompute" {:fn recompute/run
                :desc "Recompute taint propagation"
                :options recompute/cli-options}
   "convert" {:fn convert/run
              :desc "Convert legacy proof format to v4 schema"
              :options convert/cli-options}})

;; =============================================================================
;; Global Options
;; =============================================================================

(def global-options
  [["-h" "--help" "Show this help message"]
   ["-V" "--version" "Show version information"]])

(def version "0.1.0")

;; =============================================================================
;; Help & Usage
;; =============================================================================

(defn global-usage []
  (->> ["Alethfeld CLI - Semantic proof graph operations"
        ""
        "Usage: alethfeld <command> [options] [args]"
        ""
        "Commands:"
        (str/join \newline
                  (for [[cmd {:keys [desc]}] (sort commands)]
                    (format "  %-16s %s" cmd desc)))
        ""
        "Global options:"
        "  -h, --help       Show this help message"
        "  -V, --version    Show version information"
        ""
        "Run 'alethfeld <command> --help' for command-specific help."]
       (str/join \newline)))

;; =============================================================================
;; Main Entry Point
;; =============================================================================

(defn -main [& args]
  (let [;; Check for global options first
        {:keys [options arguments]} (parse-opts args global-options :in-order true)]
    (cond
      ;; Version
      (:version options)
      (do (println (str "alethfeld " version))
          (System/exit 0))

      ;; Help or no arguments
      (or (:help options) (empty? arguments))
      (do (println (global-usage))
          (System/exit (if (:help options) 0 1)))

      ;; Look up command
      :else
      (let [cmd-name (first arguments)
            cmd-args (rest arguments)
            cmd-info (get commands cmd-name)]
        (if-not cmd-info
          (do (println (str "Error: Unknown command '" cmd-name "'"))
              (println)
              (println (global-usage))
              (System/exit 2))

          ;; Parse command-specific options and run
          (let [{:keys [options arguments errors]}
                (parse-opts cmd-args (:options cmd-info))]
            (if errors
              (do (println (str "Error: " (str/join \newline errors)))
                  (System/exit 2))
              (let [result ((:fn cmd-info) arguments options)]
                (when (:message result)
                  (println (:message result)))
                (System/exit (:exit-code result))))))))))
