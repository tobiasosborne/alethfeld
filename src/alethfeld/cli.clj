(ns alethfeld.cli
  "Alethfeld CLI entry point."
  (:gen-class))

(defn -main
  "CLI entry point for Alethfeld."
  [& args]
  (println "Alethfeld v0.1.0-SNAPSHOT")
  (println "Usage: af <command> [options]")
  (println)
  (println "Commands:")
  (println "  init      Initialize .alethfeld/ in current directory")
  (println "  ready     Get next job(s) for an agent")
  (println "  show      Display mote details")
  (println "  create    Create a mote")
  (println "  help      Show this help message")
  (println)
  (println "Run 'af <command> --help' for command-specific help."))
