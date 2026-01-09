(ns alethfeld.repair
  "DAG repair operations for recovering from inconsistencies.

   Provides detection and repair of common DAG issues:
   - Orphaned motes (parent reference to non-existent mote)
   - Stale sessions (sessions referencing deleted motes)
   - Broken references (internal refs to non-existent motes)
   - Parent-child mismatches"
  (:require [alethfeld.store :as store]
            [alethfeld.dag :as dag]
            [alethfeld.session :as session]
            [alethfeld.io :as io]
            [alethfeld.path :as path]
            [clojure.string :as str]))

;; -----------------------------------------------------------------------------
;; Issue Detection
;; -----------------------------------------------------------------------------

(defn find-orphaned-parents
  "Find motes with :parent pointing to non-existent motes.

   Returns vector of maps:
   [{:mote-id \"1.1\" :orphan-parent \"1\"} ...]"
  [motes]
  (let [existing-ids (set (keys motes))]
    (->> motes
         (filter (fn [[_id mote]]
                   (and (:parent mote)
                        (not (contains? existing-ids (:parent mote))))))
         (map (fn [[id mote]]
                {:mote-id id
                 :orphan-parent (:parent mote)}))
         vec)))

(defn find-stale-sessions
  "Find active sessions referencing non-existent motes.

   Returns vector of maps:
   [{:session-id \"abc-123\" :mote-id \"missing\"} ...]"
  [repo-path motes]
  (let [existing-ids (set (keys motes))
        sessions-dir (io/full-path repo-path (path/active-sessions-path))
        session-files (io/list-edn-files sessions-dir)]
    (->> session-files
         (keep (fn [file-path]
                 ;; Extract session-id from path like ".../sessions/active/abc-123.edn"
                 (let [file-name (last (str/split file-path #"/"))
                       session-id (str/replace file-name #"\.edn$" "")
                       session (session/load-session repo-path session-id)]
                   (when (and session
                              (:mote-id session)
                              (not (contains? existing-ids (:mote-id session))))
                     {:session-id session-id
                      :mote-id (:mote-id session)
                      :agent (:agent session)}))))
         vec)))

(defn find-phantom-children
  "Find motes with :children listing non-existent motes.

   Returns vector of maps:
   [{:parent-id \"1\" :phantom-children [\"1.1\" \"1.2\"]} ...]"
  [motes]
  (let [existing-ids (set (keys motes))]
    (->> motes
         (filter (fn [[_id mote]]
                   (some #(not (contains? existing-ids %)) (:children mote))))
         (map (fn [[id mote]]
                {:parent-id id
                 :phantom-children (vec (filter #(not (contains? existing-ids %))
                                                (:children mote)))}))
         vec)))

(defn detect-issues
  "Detect all DAG and session issues.

   Returns map with:
   - :orphaned-parents - motes with missing parent refs
   - :stale-sessions - sessions referencing missing motes
   - :phantom-children - motes with missing children refs
   - :broken-refs - internal refs to non-existent motes
   - :cycles - cycle in dependency graph (if any)
   - :total-issues - count of all issues"
  [repo-path]
  (let [motes (store/load-all-motes repo-path :include-archived true)

        ;; Use existing DAG validation
        dag-result (dag/validate-mote-graph motes)
        dag-errors (:errors dag-result)

        ;; Extract specific error types from DAG validation
        broken-refs-err (first (filter #(= :broken-refs (:category %)) dag-errors))
        cycle-err (first (filter #(= :cycle (:category %)) dag-errors))

        ;; Additional repair-specific detection
        orphaned-parents (find-orphaned-parents motes)
        stale-sessions (find-stale-sessions repo-path motes)
        phantom-children (find-phantom-children motes)]

    {:orphaned-parents orphaned-parents
     :stale-sessions stale-sessions
     :phantom-children phantom-children
     :broken-refs (:broken-refs broken-refs-err)
     :cycle (:cycle cycle-err)
     :total-issues (+ (count orphaned-parents)
                      (count stale-sessions)
                      (count phantom-children)
                      (count (:broken-refs broken-refs-err))
                      (if cycle-err 1 0))}))

;; -----------------------------------------------------------------------------
;; Repair Operations
;; -----------------------------------------------------------------------------

(defn repair-orphaned-parent!
  "Repair an orphaned parent reference by clearing the parent field.

   Arguments:
   - repo-path: Path to repository
   - mote-id: ID of mote with orphaned parent

   Returns the updated mote."
  [repo-path mote-id]
  (let [mote (store/load-mote repo-path mote-id)]
    (when mote
      (let [updated (dissoc mote :parent)]
        (store/save-mote! repo-path updated)
        updated))))

(defn repair-stale-session!
  "Repair a stale session by archiving it.

   Arguments:
   - repo-path: Path to repository
   - session-id: ID of stale session

   Returns true if session was archived."
  [repo-path session-id]
  (let [session (session/load-session repo-path session-id)]
    (when session
      (session/archive-session! repo-path session-id)
      true)))

(defn repair-phantom-children!
  "Repair phantom children by removing non-existent IDs from :children.

   Arguments:
   - repo-path: Path to repository
   - parent-id: ID of parent mote with phantom children

   Returns the updated mote."
  [repo-path parent-id]
  (let [motes (store/load-all-motes repo-path :include-archived true)
        existing-ids (set (keys motes))
        parent (get motes parent-id)]
    (when parent
      (let [valid-children (vec (filter #(contains? existing-ids %) (:children parent)))
            updated (assoc parent :children valid-children)]
        (store/save-mote! repo-path updated)
        updated))))

(defn repair-broken-ref!
  "Repair a broken reference by removing it from the mote's assumptions.

   Arguments:
   - repo-path: Path to repository
   - mote-id: ID of mote with broken ref
   - broken-ref: The broken reference ID to remove

   Returns the updated mote."
  [repo-path mote-id broken-ref]
  (let [mote (store/load-mote repo-path mote-id)]
    (when mote
      (let [;; Remove from assumptions
            updated-assumptions (vec (remove #(and (= :internal (:type %))
                                                   (= broken-ref (:ref %)))
                                             (:assumptions mote)))
            ;; Remove from depends-on
            updated-depends (vec (remove #(= broken-ref (:ref %))
                                         (:depends-on mote)))
            updated (assoc mote
                           :assumptions updated-assumptions
                           :depends-on updated-depends)]
        (store/save-mote! repo-path updated)
        updated))))

;; -----------------------------------------------------------------------------
;; Repair Execution
;; -----------------------------------------------------------------------------

(defn execute-repairs!
  "Execute all automatic repairs.

   Arguments:
   - repo-path: Path to repository
   - issues: Issue map from detect-issues

   Returns map with:
   - :repaired-orphans - count of orphaned parents fixed
   - :repaired-sessions - count of stale sessions completed
   - :repaired-phantoms - count of phantom children fixed
   - :repaired-refs - count of broken refs removed
   - :unrepaired-cycle - true if cycle exists (requires manual fix)"
  [repo-path issues]
  (let [;; Repair orphaned parents
        repaired-orphans
        (count (keep #(repair-orphaned-parent! repo-path (:mote-id %))
                     (:orphaned-parents issues)))

        ;; Repair stale sessions
        repaired-sessions
        (count (keep #(repair-stale-session! repo-path (:session-id %))
                     (:stale-sessions issues)))

        ;; Repair phantom children
        repaired-phantoms
        (count (keep #(repair-phantom-children! repo-path (:parent-id %))
                     (:phantom-children issues)))

        ;; Repair broken refs
        repaired-refs
        (count (keep (fn [{:keys [mote-id ref]}]
                       (repair-broken-ref! repo-path mote-id ref))
                     (:broken-refs issues)))]

    {:repaired-orphans repaired-orphans
     :repaired-sessions repaired-sessions
     :repaired-phantoms repaired-phantoms
     :repaired-refs repaired-refs
     :unrepaired-cycle (boolean (:cycle issues))}))

;; -----------------------------------------------------------------------------
;; Formatting
;; -----------------------------------------------------------------------------

(defn format-issues
  "Format detected issues for display."
  [issues]
  (let [lines (cond-> []
                ;; Orphaned parents
                (seq (:orphaned-parents issues))
                (into (cons "Orphaned parent references:"
                            (map #(str "  - " (:mote-id %) " → missing parent " (:orphan-parent %))
                                 (:orphaned-parents issues))))

                ;; Stale sessions
                (seq (:stale-sessions issues))
                (into (cons "Stale sessions:"
                            (map #(str "  - session " (:session-id %) " → missing mote " (:mote-id %))
                                 (:stale-sessions issues))))

                ;; Phantom children
                (seq (:phantom-children issues))
                (into (cons "Phantom children:"
                            (map #(str "  - " (:parent-id %) " lists missing: " (str/join ", " (:phantom-children %)))
                                 (:phantom-children issues))))

                ;; Broken refs
                (seq (:broken-refs issues))
                (into (cons "Broken references:"
                            (map #(str "  - " (:mote-id %) " → missing " (:ref-type %) " " (:ref %))
                                 (:broken-refs issues))))

                ;; Cycles
                (:cycle issues)
                (conj (str "Dependency cycle detected: " (str/join " → " (:cycle issues)))))]
    (if (seq lines)
      (str/join "\n" lines)
      "No issues found.")))

(defn format-repairs
  "Format repair results for display."
  [repairs]
  (let [lines (cond-> []
                (pos? (:repaired-orphans repairs))
                (conj (str "Fixed " (:repaired-orphans repairs) " orphaned parent references"))

                (pos? (:repaired-sessions repairs))
                (conj (str "Completed " (:repaired-sessions repairs) " stale sessions"))

                (pos? (:repaired-phantoms repairs))
                (conj (str "Fixed " (:repaired-phantoms repairs) " phantom children references"))

                (pos? (:repaired-refs repairs))
                (conj (str "Removed " (:repaired-refs repairs) " broken references"))

                (:unrepaired-cycle repairs)
                (conj "WARNING: Dependency cycle requires manual resolution"))]
    (if (seq lines)
      (str/join "\n" lines)
      "No repairs needed.")))
