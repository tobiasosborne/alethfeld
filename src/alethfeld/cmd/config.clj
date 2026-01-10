(ns alethfeld.cmd.config
  "Config command implementation."
  (:require [alethfeld.cmd.core :as core]
            [alethfeld.store :as store]
            [alethfeld.tx :as tx]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Config Keys Definition
;; -----------------------------------------------------------------------------

(def ^:private config-keys
  "Valid configuration keys with their types and defaults."
  {:project-name {:type :string :default "Unnamed Proof"}
   :version {:type :string :default "0.1"}
   :default-difficulty {:type :int :min 1 :max 5 :default 3}
   :proposal-quorum {:type :int :min 1 :default 1}
   :vote-quorum {:type :int :min 1 :default 1}
   :claim-timeout-minutes {:type :int :min 1 :default 30}})

;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(defn- parse-config-value
  "Parse a string value to the appropriate type for a config key."
  [key-name value-str]
  (let [key-kw (keyword key-name)
        spec (get config-keys key-kw)]
    (when-not spec
      (throw (ex-info "Unknown config key"
                      {:type :validation-failed
                       :errors [(str "Unknown config key: " key-name
                                     ". Valid keys: " (str/join ", " (map name (keys config-keys))))]})))
    (case (:type spec)
      :string value-str
      :int (let [parsed (parse-long value-str)]
             (when-not parsed
               (throw (ex-info "Invalid integer value"
                               {:type :validation-failed
                                :errors [(str "Expected integer for " key-name ", got: " value-str)]})))
             (when (and (:min spec) (< parsed (:min spec)))
               (throw (ex-info "Value below minimum"
                               {:type :validation-failed
                                :errors [(str key-name " must be >= " (:min spec))]})))
             (when (and (:max spec) (> parsed (:max spec)))
               (throw (ex-info "Value above maximum"
                               {:type :validation-failed
                                :errors [(str key-name " must be <= " (:max spec))]})))
             parsed))))

;; -----------------------------------------------------------------------------
;; Command Implementation
;; -----------------------------------------------------------------------------

(defn cmd-config
  "Manage project configuration.

   Subcommands:
   - list: Show all configuration
   - get <key>: Get a specific value
   - set <key> <value>: Set a value

   Valid keys:
   - project-name (string)
   - version (string)
   - default-difficulty (1-5)
   - proposal-quorum (integer >= 1)
   - vote-quorum (integer >= 1)
   - claim-timeout-minutes (integer >= 1)"
  [{:keys [id args repo-path] :or {repo-path "."}}]
  (let [subcommand id]

    ;; Check repository exists
    (when-not (store/repo-exists? repo-path)
      (throw (ex-info "Not an Alethfeld repository"
                      {:type :not-initialized
                       :path repo-path})))

    (case subcommand
      ;; List all config
      ("list" nil)
      (let [config (store/load-config repo-path)]
        {:config config
         :keys (keys config-keys)
         :next-actions [(core/make-action "af config set <key> <value>" "Update a config value")
                        (core/status-action)]})

      ;; Get a specific key
      "get"
      (let [key-name (first args)]
        (when-not key-name
          (throw (ex-info "Config key required"
                          {:type :validation-failed
                           :errors ["Usage: af config get <key>"]})))
        (let [key-kw (keyword key-name)
              config (store/load-config repo-path)
              spec (get config-keys key-kw)]
          (when-not spec
            (throw (ex-info "Unknown config key"
                            {:type :validation-failed
                             :errors [(str "Unknown config key: " key-name
                                           ". Valid keys: " (str/join ", " (map name (keys config-keys))))]})))
          {:key key-kw
           :value (get config key-kw (:default spec))
           :default (:default spec)
           :next-actions [(core/make-action (str "af config set " key-name " <value>") "Change this value")
                          (core/make-action "af config list" "View all config")]}))

      ;; Set a key
      "set"
      (let [key-name (first args)
            value-str (second args)]
        (when-not key-name
          (throw (ex-info "Config key required"
                          {:type :validation-failed
                           :errors ["Usage: af config set <key> <value>"]})))
        (when-not value-str
          (throw (ex-info "Config value required"
                          {:type :validation-failed
                           :errors ["Usage: af config set <key> <value>"]})))
        (let [key-kw (keyword key-name)
              parsed-value (parse-config-value key-name value-str)
              config (store/load-config repo-path)
              new-config (assoc config key-kw parsed-value)]
          (tx/atomic-write-config! repo-path
                                   (str "Set config: " key-name " = " parsed-value)
                                   new-config)
          {:key key-kw
           :value parsed-value
           :previous (get config key-kw)
           :message (str "Config updated: " key-name " = " parsed-value)
           :next-actions [(core/make-action "af config list" "View all config")
                          (core/status-action)]}))

      ;; Unknown subcommand
      (throw (ex-info "Unknown config subcommand"
                      {:type :validation-failed
                       :errors [(str "Unknown subcommand: " subcommand
                                     ". Use: list, get, set")]})))))
