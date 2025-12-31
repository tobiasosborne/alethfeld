(ns alethfeld.schema.primitives
  "Primitive schemas for Alethfeld semantic proof graphs.
   These are the basic building blocks used by other schema modules."
  (:require [alethfeld.config :as config]))

;; =============================================================================
;; Primitive Schemas
;; =============================================================================

(def NodeId
  "Node IDs are keywords with format :<depth>-<uuid-prefix> or special like :theorem"
  :keyword)

(def ContentHash
  "SHA256 hash prefix (configurable length hex string)"
  [:re {:error/message (str "Content hash must be " config/content-hash-length " lowercase hex characters")}
   config/content-hash-pattern])

(def ISO8601
  "ISO 8601 datetime string"
  [:re {:error/message "Must be ISO 8601 format: YYYY-MM-DDTHH:MM:SS"}
   #"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}"])

(def LaTeXString
  "LaTeX mathematical statement (non-empty string)"
  [:string {:min 1 :error/message "Statement must be a non-empty string"}])
