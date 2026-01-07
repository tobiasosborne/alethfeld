(ns alethfeld.result
  "Unified result handling for ops and commands.

   Result types:
   - Success: {:ok data}
   - Failure: {:error errors}  where errors is string or vector of error maps

   Exit codes:
   - 0: Success
   - 1: Operation failed (logic error, precondition violation)
   - 2: Input error (file not found, parse error)")

;; =============================================================================
;; Constructors
;; =============================================================================

(defn ok
  "Wrap a value in a success result."
  [value]
  {:ok value})

(defn err
  "Wrap errors in a failure result.
   Errors can be a string or vector of error maps."
  [errors]
  {:error errors})

;; =============================================================================
;; Predicates
;; =============================================================================

(defn ok?
  "Returns true if result is a success."
  [result]
  (contains? result :ok))

(defn err?
  "Returns true if result is a failure."
  [result]
  (contains? result :error))

;; =============================================================================
;; Accessors
;; =============================================================================

(defn unwrap
  "Get the :ok value or throw if error."
  [result]
  (if (ok? result)
    (:ok result)
    (throw (ex-info "Attempted to unwrap error result" {:error (:error result)}))))

(defn unwrap-or
  "Get the :ok value or return default if error."
  [result default]
  (if (ok? result)
    (:ok result)
    default))

;; =============================================================================
;; Monadic Operations
;; =============================================================================

(defn bind
  "Chain a function over a result. Short-circuits on error.
   (bind {:ok 1} inc) => {:ok 2}
   (bind {:error e} inc) => {:error e}"
  [result f]
  (if (ok? result)
    (f (:ok result))
    result))

(defn fmap
  "Map a function over the :ok value, keeping errors unchanged.
   Unlike bind, f returns a plain value, not a result."
  [result f]
  (if (ok? result)
    {:ok (f (:ok result))}
    result))

(defmacro let-ok
  "Bind multiple results in sequence, short-circuiting on first error.

   (let-ok [graph (io/read-graph path)
            node  (io/read-edn node-path)]
     (ops/add-node graph node))

   Equivalent to nested bind calls but more readable."
  [bindings & body]
  (if (empty? bindings)
    `(do ~@body)
    (let [[sym expr & rest] bindings]
      `(bind ~expr (fn [~sym] (let-ok ~(vec rest) ~@body))))))

;; =============================================================================
;; Error Formatting
;; =============================================================================

(defn format-io-error
  "Format an I/O error (string) for CLI output."
  [error-str prefix]
  (str prefix ": " error-str))

(defn format-op-errors
  "Format operation errors (vector of maps) for CLI output."
  [errors]
  (clojure.string/join
   "\n"
   (map (fn [e] (str "  [" (name (:type e)) "] " (:message e)))
        errors)))

;; =============================================================================
;; Exit Code Conversion
;; =============================================================================

(defn to-exit
  "Convert a result to command exit format {:exit-code :message}.

   Options:
   - :success-fn - Function (data -> message) for success case
   - :io-error?  - If true, errors use exit-code 2 (input error)
                   If false (default), errors use exit-code 1 (op error)"
  [result & {:keys [success-fn io-error?]
             :or {success-fn str
                  io-error? false}}]
  (if (ok? result)
    {:exit-code 0
     :message (success-fn (:ok result))}
    (let [errors (:error result)
          exit-code (if io-error? 2 1)]
      {:exit-code exit-code
       :message (if (string? errors)
                  (str "Error: " errors)
                  (str "Error: Operation failed\n" (format-op-errors errors)))})))

(defn exit-ok
  "Create a success exit result."
  [message]
  {:exit-code 0 :message message})

(defn exit-err
  "Create an error exit result."
  [exit-code message]
  {:exit-code exit-code :message message})

;; =============================================================================
;; Convenience Combinators
;; =============================================================================

(defn try-io
  "Wrap an I/O operation, returning error with exit-code context.
   Used for read operations that should fail with exit-code 2."
  [io-result error-prefix]
  (if (ok? io-result)
    io-result
    {:error {:exit-code 2
             :message (format-io-error (:error io-result) error-prefix)}}))

(defn try-op
  "Wrap an operation result with exit-code context.
   Used for ops that should fail with exit-code 1."
  [op-result]
  (if (ok? op-result)
    op-result
    {:error {:exit-code 1
             :message (str "Error: Operation failed\n"
                           (format-op-errors (:error op-result)))}}))

(defn to-final-exit
  "Convert a result with embedded exit info to final exit format.
   For use after try-io/try-op pipeline."
  [result success-message]
  (if (ok? result)
    {:exit-code 0 :message success-message}
    {:exit-code (get-in result [:error :exit-code] 1)
     :message (get-in result [:error :message] "Unknown error")}))
