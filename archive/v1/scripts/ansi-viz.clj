#!/usr/bin/env bb
;; Elegant ANSI visualization for alethfeld proof graphs
;; Color scheme: Nord-inspired with semantic meaning

(require '[clojure.edn :as edn]
         '[clojure.string :as str])

;; =============================================================================
;; Color Palette - Nord-inspired with semantic hierarchy
;; =============================================================================
;;
;; The palette uses a restrained approach:
;; - Structural elements (assumptions, definitions) in cool tones
;; - Active proof work (claims) in neutral/warm
;; - Status indicated by intensity, not hue proliferation
;; - Taint/problems in a single warning color
;;
;; ANSI 256-color codes for precise control:
;;   \u001b[38;5;Nm  - foreground color N
;;   \u001b[48;5;Nm  - background color N

(def colors
  {;; Node types - semantic spectrum from foundation → conclusion
   :assumption      "\u001b[38;5;109m"   ; steel blue - foundational, given
   :local-assume    "\u001b[38;5;109m"   ; same family
   :local-discharge "\u001b[38;5;139m"   ; muted lavender - scope closure
   :definition      "\u001b[38;5;179m"   ; warm sand - definitions ground things
   :claim           "\u001b[38;5;252m"   ; near-white - the actual work
   :lemma-ref       "\u001b[38;5;108m"   ; sage - external/proven
   :external-ref    "\u001b[38;5;108m"   ; sage
   :qed             "\u001b[38;5;150m"   ; soft green - success/completion
   
   ;; Status - simple: good/pending/problem
   :verified        "\u001b[38;5;150m"   ; soft green
   :proposed        "\u001b[38;5;223m"   ; warm cream - not yet done
   :admitted        "\u001b[38;5;216m"   ; peach - needs attention  
   :rejected        "\u001b[38;5;174m"   ; dusty rose - problem
   
   ;; Taint
   :clean           ""
   :tainted         "\u001b[38;5;174m"   ; dusty rose
   :self-admitted   "\u001b[38;5;216m"   ; peach
   
   ;; Structural
   :dim             "\u001b[38;5;242m"   ; gray for secondary info
   :dimmer          "\u001b[38;5;238m"   ; darker gray for structure
   :title           "\u001b[38;5;255m"   ; bright white
   :theorem         "\u001b[38;5;223m"   ; warm cream for theorem
   :border          "\u001b[38;5;240m"   ; subtle border color
   
   ;; Emphasis
   :bold            "\u001b[1m"
   :reset           "\u001b[0m"})

;; =============================================================================
;; Symbols - Minimalist geometric vocabulary
;; =============================================================================

(def node-symbols
  {:assumption      "◇"    ; diamond - given/external
   :local-assume    "◇"    
   :local-discharge "▹"    ; small triangle - discharge
   :definition      "≡"    ; equivalence - definition
   :claim           "•"    ; bullet - proof step
   :lemma-ref       "◆"    ; filled diamond - solid external
   :external-ref    "◆"    
   :qed             "■"})  ; filled square - done

(def status-symbols
  {:verified  "✓"
   :proposed  "○"
   :admitted  "?"
   :rejected  "✗"})

(def taint-markers
  {:clean        ""
   :tainted      "!"
   :self-admitted "~"})

;; Box drawing - elegant thin lines
(def box
  {:h "─" :v "│" :tl "┌" :tr "┐" :bl "└" :br "┘"
   :t "┬" :b "┴" :l "├" :r "┤" :x "┼"
   :dot "·"})

;; =============================================================================
;; Helpers
;; =============================================================================

(defn c [& ks]
  "Compose color codes"
  (apply str (map #(get colors % "") ks)))

(defn truncate [s n]
  (if (> (count s) n)
    (str (subs s 0 (- n 1)) "…")
    s))

(defn clean-statement [s max-len]
  (-> s
      (str/replace #"\*\*([^*]+)\*\*" "$1")  ; remove bold markers, keep text
      (str/replace #"\$([^$]+)\$" "$1")       ; keep math content
      (str/replace #"\\[a-z]+\{([^}]*)\}" "$1") ; \cmd{x} → x
      (str/replace #"\\\\" " ")               ; \\ → space
      (str/replace #"\\([a-zA-Z]+)" "")       ; remove remaining commands
      (str/replace #"\s+" " ")                ; collapse whitespace
      str/trim
      (truncate max-len)))

(defn sort-nodes [nodes]
  (sort-by (fn [[_ n]] [(:display-order n 0) (:depth n 0)]) nodes))

(defn repeat-str [s n]
  (apply str (repeat n s)))

;; =============================================================================
;; Tree structure rendering
;; =============================================================================

(defn make-tree-prefix 
  "Generate tree prefix for a node based on its position in sibling list.
   Returns [connector indent-continuation]"
  [depth is-last? prev-depths]
  (if (zero? depth)
    ["" ""]
    (let [;; Build the indent based on whether ancestors were last in their groups
          indent (apply str 
                        (for [d (range (dec depth))]
                          (if (get prev-depths d false)
                            "    "                              ; ancestor was last, no line
                            (str (c :dimmer) "│   " (c :reset)))))  ; ancestor continues
          connector (if is-last?
                      (str (c :dimmer) "└── " (c :reset))
                      (str (c :dimmer) "├── " (c :reset)))]
      [connector indent])))

;; =============================================================================
;; Main renderer
;; =============================================================================

(defn render-node [node depth tree-prefix max-width]
  (let [type-color (c (:type node))
        status-color (c (:status node))
        symbol (get node-symbols (:type node) "?")
        status-sym (get status-symbols (:status node) "?")
        taint-mark (get taint-markers (:taint node) "")
        
        ;; Format: prefix symbol status id: statement
        id-str (name (:id node))
        prefix-len (+ (count tree-prefix) 8 (count id-str))  ; rough estimate
        available (- max-width prefix-len 2)
        statement (clean-statement (:statement node) (max 20 available))]
    
    (str tree-prefix
         type-color symbol (c :reset) " "
         status-color status-sym (c :reset)
         (when (seq taint-mark) (str (c :tainted) taint-mark (c :reset)))
         " "
         (c :dim) id-str (c :reset) 
         (c :dimmer) ": " (c :reset)
         statement)))

(defn render-graph [g & {:keys [width] :or {width 100}}]
  (let [sorted (sort-nodes (:nodes g))
        nodes-vec (vec sorted)
        n-nodes (count sorted)
        
        ;; Group nodes by depth to determine tree structure
        ;; For simplicity, we'll use display-order to infer parent-child
        ;; A node at depth d+1 following a node at depth d is its child
        
        ;; Count stats
        n-verified (count (filter #(= :verified (:status (val %))) (:nodes g)))
        n-admitted (count (filter #(= :admitted (:status (val %))) (:nodes g)))
        n-tainted (count (filter #(#{:tainted :self-admitted} (:taint (val %))) (:nodes g)))
        
        ;; Build header
        border-line (str (c :border) (repeat-str (box :h) width) (c :reset))
        
        header (str
                "\n"
                (c :bold :title) (:graph-id g) (c :reset)
                (c :dim) "  v" (:version g) 
                " · " n-nodes " nodes"
                " · " n-verified "/" n-nodes " verified"
                (when (pos? n-admitted) (str " · " (c :admitted) n-admitted " admitted" (c :reset :dim)))
                (when (pos? n-tainted) (str " · " (c :tainted) n-tainted " tainted" (c :reset :dim)))
                (c :reset)
                "\n"
                border-line
                "\n\n"
                (c :theorem) "THEOREM: " (c :reset)
                (clean-statement (get-in g [:theorem :statement]) (- width 10))
                "\n\n")
        
        ;; Render nodes with tree structure
        ;; Track which depths have continuing siblings
        node-lines 
        (loop [i 0
               lines []
               continuing-depths #{}]  ; depths that have more siblings coming
          (if (>= i n-nodes)
            lines
            (let [[node-id node] (nth nodes-vec i)
                  depth (:depth node 0)
                  
                  ;; Look ahead to see if there are more nodes at same depth
                  ;; (siblings in the tree sense)
                  has-sibling-after? 
                  (some (fn [j]
                          (let [[_ future-node] (nth nodes-vec j)]
                            (= depth (:depth future-node 0))))
                        (range (inc i) (min (+ i 10) n-nodes)))
                  
                  ;; Is this the last node at this depth in current subtree?
                  is-last? (not has-sibling-after?)
                  
                  ;; Build tree prefix
                  indent (apply str 
                                (for [d (range depth)]
                                  (if (contains? continuing-depths d)
                                    (str (c :dimmer) "│   " (c :reset))
                                    "    ")))
                  connector (cond
                              (zero? depth) ""
                              is-last? (str (c :dimmer) "└── " (c :reset))
                              :else (str (c :dimmer) "├── " (c :reset)))
                  tree-prefix (str indent connector)
                  
                  ;; Update continuing depths
                  new-continuing (if is-last?
                                   (disj continuing-depths depth)
                                   (conj continuing-depths depth))
                  ;; Clear deeper levels when we go back up
                  new-continuing (into #{} (filter #(< % depth) new-continuing))
                  new-continuing (if has-sibling-after?
                                   (conj new-continuing depth)
                                   new-continuing)]
              
              (recur (inc i)
                     (conj lines (render-node node depth tree-prefix width))
                     new-continuing))))
        
        ;; Legend
        legend (str "\n"
                    border-line
                    "\n"
                    (c :dim)
                    "◇ assumption  ≡ definition  • claim  ◆ external  ■ qed"
                    "   │   "
                    (c :verified) "✓" (c :dim) " verified  "
                    (c :admitted) "?" (c :dim) " admitted  "
                    (c :rejected) "✗" (c :dim) " rejected"
                    (c :reset)
                    "\n")]
    
    (str header
         (str/join "\n" node-lines)
         legend)))

;; =============================================================================
;; Summary one-liner
;; =============================================================================

(defn render-summary [g]
  (let [nodes (:nodes g)
        n (count nodes)
        v (count (filter #(= :verified (:status (val %))) nodes))
        t (count (filter #(#{:tainted :self-admitted} (:taint (val %))) nodes))
        complete? (and (zero? t) (= n v) (some #(= :qed (:type (val %))) nodes))]
    (str (c :dim) (:graph-id g) (c :reset)
         " │ " n " nodes │ "
         (if (= n v)
           (str (c :verified) v "/" n " ✓" (c :reset))
           (str v "/" n))
         (if (zero? t)
           (str " │ " (c :verified) "clean" (c :reset))
           (str " │ " (c :tainted) t " tainted" (c :reset)))
         (when complete? (str " │ " (c :bold :verified) "COMPLETE" (c :reset))))))

;; =============================================================================
;; Main
;; =============================================================================

(defn -main [& args]
  (when (or (empty? args) (= (first args) "--help") (= (first args) "-h"))
    (println "Usage: ansi-viz.clj <proof-graph.edn> [summary]")
    (println "  <proof-graph.edn>  Path to the EDN proof graph file.")
    (println "  summary            (Optional) Print a one-line summary instead of the full tree.")
    (System/exit 0))

  (let [graph-file (first args)
        mode (second args)]
    (if (.exists (java.io.File. graph-file))
      (let [g (edn/read-string (slurp graph-file))]
        (case mode
          "summary" (println (render-summary g))
          (println (render-graph g :width 95))))
      (do
        (println "File not found:" graph-file)
        (System/exit 1)))))

(-main (first *command-line-args*) (second *command-line-args*))
