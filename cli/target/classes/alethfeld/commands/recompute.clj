(ns alethfeld.commands.recompute
  "CLI command for recomputing taint propagation in a graph."
  (:require [clojure.string :as str]
            [alethfeld.io :as io]
            [alethfeld.graph :as graph]))

(def cli-options
  [["-d" "--dry-run" "Show what would change without modifying"]
   ["-o" "--output FILE" "Write to a different file"]
   ["-h" "--help" "Show help for recompute command"]])

(defn usage []
  (->> ["Recompute taint propagation in a semantic proof graph."
        ""
        "Usage: alethfeld recompute [options] <graph.edn>"
        ""
        "Arguments:"
        "  graph.edn    The graph file to process"
        ""
        "Options:"
        "  -d, --dry-run    Show what would change without writing"
        "  -o, --output F   Write to different file (default: overwrite input)"
        "  -h, --help       Show this help"
        ""
        "This command:"
        "  1. Traverses nodes in topological order"
        "  2. Recomputes taint based on node status and dependencies"
        "  3. Updates :self-admitted for :admitted nodes"
        "  4. Propagates :tainted from dependencies"
        ""
        "Exit codes:"
        "  0 - Success"
        "  2 - Input error (file not found, parse error)"]
       (str/join \newline)))

(defn- find-taint-changes
  "Find nodes where computed taint differs from stored taint."
  [g]
  (let [nodes (:nodes g)]
    (->> nodes
         (map (fn [[nid node]]
                (let [computed (graph/compute-taint g nid)
                      stored (:taint node)]
                  (when (not= computed stored)
                    {:node-id nid
                     :old-taint stored
                     :new-taint computed}))))
         (remove nil?)
         vec)))

(defn run
  "Run the recompute command."
  [args options]
  (cond
    (:help options)
    {:exit-code 0 :message (usage)}

    (empty? args)
    {:exit-code 2 :message (str "Error: No graph file specified\n\n" (usage))}

    :else
    (let [graph-path (first args)
          graph-result (io/read-graph graph-path)]

      (if (:error graph-result)
        {:exit-code 2 :message (str "Error reading graph: " (:error graph-result))}

        (let [original-graph (:ok graph-result)
              changes (find-taint-changes original-graph)
              recomputed-graph (-> original-graph
                                   graph/recompute-all-taints
                                   graph/increment-version
                                   graph/update-last-modified)]

          (cond
            (empty? changes)
            {:exit-code 0
             :message (io/format-edn
                       {:status :ok
                        :message "No taint changes needed"
                        :nodes-checked (count (:nodes original-graph))})}

            (:dry-run options)
            {:exit-code 0
             :message (io/format-edn
                       {:status :ok
                        :message "Dry run - would update taint"
                        :changes-count (count changes)
                        :changes changes})}

            :else
            (let [output-path (or (:output options) graph-path)
                  write-result (io/write-graph output-path recomputed-graph)]
              (if (:error write-result)
                {:exit-code 2 :message (str "Error writing graph: " (:error write-result))}
                {:exit-code 0
                 :message (io/format-edn
                           {:status :ok
                            :message "Taint recomputed"
                            :changes-count (count changes)
                            :graph-version (:version recomputed-graph)})}))))))))
