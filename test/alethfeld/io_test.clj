(ns alethfeld.io-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [babashka.fs :as fs]
            [alethfeld.io :as io]))

;; -----------------------------------------------------------------------------
;; Test Fixtures
;; -----------------------------------------------------------------------------

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture
  "Creates a temp directory for each test and cleans up after."
  [f]
  (let [temp (fs/create-temp-dir {:prefix "alethfeld-test-"})]
    (try
      (binding [*temp-dir* temp]
        (f))
      (finally
        (fs/delete-tree temp)))))

(use-fixtures :each temp-dir-fixture)

(defn- temp-path
  "Create a path within the temp directory."
  [& parts]
  (str (apply fs/path *temp-dir* parts)))

;; =============================================================================
;; read-edn Tests
;; =============================================================================

(deftest read-edn-file-exists-test
  (testing "Reads valid EDN from file"
    (let [path (temp-path "test.edn")
          data {:foo "bar" :count 42}]
      (spit path (pr-str data))
      (is (= data (io/read-edn path))))))

(deftest read-edn-complex-data-test
  (testing "Reads complex nested EDN"
    (let [path (temp-path "complex.edn")
          data {:id "1.2.3"
                :children ["1.2.3.1" "1.2.3.2"]
                :taint #{:needs-verification :needs-refs}
                :votes [{:agent "v1" :vote :for}
                        {:agent "v2" :vote :against}]}]
      (spit path (pr-str data))
      (is (= data (io/read-edn path))))))

(deftest read-edn-file-not-exists-test
  (testing "Returns nil for non-existent file"
    (is (nil? (io/read-edn (temp-path "nonexistent.edn"))))))

(deftest read-edn-invalid-edn-test
  (testing "Throws for invalid EDN"
    (let [path (temp-path "invalid.edn")]
      (spit path "{ this is not valid EDN }")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Failed to parse"
                            (io/read-edn path))))))

(deftest read-edn-parse-error-info-test
  (testing "Parse error includes path information"
    (let [path (temp-path "bad.edn")]
      (spit path "{:incomplete")
      (try
        (io/read-edn path)
        (is false "Should have thrown")
        (catch clojure.lang.ExceptionInfo e
          (is (= :parse-error (:type (ex-data e))))
          (is (= path (:path (ex-data e)))))))))

(deftest read-edn-empty-file-test
  (testing "Returns nil for empty file (no EDN forms)"
    (let [path (temp-path "empty.edn")]
      (spit path "")
      (is (nil? (io/read-edn path))))))

(deftest read-edn-with-comments-test
  (testing "Reads EDN with comments"
    (let [path (temp-path "comments.edn")
          content "; This is a comment\n{:key \"value\"}\n; End"]
      (spit path content)
      (is (= {:key "value"} (io/read-edn path))))))

;; =============================================================================
;; write-edn Tests
;; =============================================================================

(deftest write-edn-basic-test
  (testing "Writes data to file"
    (let [path (temp-path "output.edn")
          data {:name "test" :value 123}]
      (io/write-edn path data)
      (is (fs/exists? path))
      (is (= data (io/read-edn path))))))

(deftest write-edn-creates-dirs-test
  (testing "Creates parent directories if needed"
    (let [path (temp-path "nested" "deep" "output.edn")
          data {:nested true}]
      (io/write-edn path data)
      (is (fs/exists? path))
      (is (= data (io/read-edn path))))))

(deftest write-edn-overwrites-test
  (testing "Overwrites existing file"
    (let [path (temp-path "overwrite.edn")]
      (io/write-edn path {:version 1})
      (io/write-edn path {:version 2})
      (is (= {:version 2} (io/read-edn path))))))

(deftest write-edn-returns-path-test
  (testing "Returns the path written to"
    (let [path (temp-path "return.edn")]
      (is (= path (io/write-edn path {:data true}))))))

(deftest write-edn-roundtrip-test
  (testing "Data survives write/read roundtrip"
    (let [path (temp-path "roundtrip.edn")
          data {:id "1.2.3"
                :claim "For all ε > 0..."
                :status :fixed
                :taint #{:needs-verification}
                :priority :p1
                :difficulty 3
                :children []
                :assumptions [{:type :internal :ref "1.1"}]
                :definitions [{:symbol "ε" :meaning "epsilon"}]
                :votes []}]
      (io/write-edn path data)
      (is (= data (io/read-edn path))))))

(deftest write-edn-unicode-test
  (testing "Handles unicode characters"
    (let [path (temp-path "unicode.edn")
          data {:greek "αβγδεζηθ"
                :math "∀∃∈∉∅"
                :emoji "🎯"}]
      (io/write-edn path data)
      (is (= data (io/read-edn path))))))

;; =============================================================================
;; delete-file Tests
;; =============================================================================

(deftest delete-file-exists-test
  (testing "Deletes existing file and returns true"
    (let [path (temp-path "to-delete.edn")]
      (spit path "data")
      (is (fs/exists? path))
      (is (true? (io/delete-file path)))
      (is (not (fs/exists? path))))))

(deftest delete-file-not-exists-test
  (testing "Returns false for non-existent file"
    (is (false? (io/delete-file (temp-path "nonexistent.edn"))))))

(deftest delete-file-directory-test
  (testing "Does not delete directories"
    (let [dir (temp-path "some-dir")]
      (fs/create-dirs dir)
      (is (false? (io/delete-file dir)))
      (is (fs/exists? dir)))))

;; =============================================================================
;; move-file Tests
;; =============================================================================

(deftest move-file-basic-test
  (testing "Moves file from src to dst"
    (let [src (temp-path "source.edn")
          dst (temp-path "dest.edn")
          data {:moved true}]
      (io/write-edn src data)
      (io/move-file src dst)
      (is (not (fs/exists? src)))
      (is (fs/exists? dst))
      (is (= data (io/read-edn dst))))))

(deftest move-file-creates-dirs-test
  (testing "Creates destination directories if needed"
    (let [src (temp-path "file.edn")
          dst (temp-path "new" "nested" "dir" "file.edn")
          data {:nested-move true}]
      (io/write-edn src data)
      (io/move-file src dst)
      (is (not (fs/exists? src)))
      (is (= data (io/read-edn dst))))))

(deftest move-file-returns-dst-test
  (testing "Returns destination path"
    (let [src (temp-path "a.edn")
          dst (temp-path "b.edn")]
      (spit src "data")
      (is (= dst (io/move-file src dst))))))

(deftest move-file-not-found-test
  (testing "Throws for non-existent source"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Source file not found"
                          (io/move-file (temp-path "missing.edn")
                                        (temp-path "dest.edn"))))))

(deftest move-file-error-info-test
  (testing "Error includes path information"
    (let [src (temp-path "nope.edn")]
      (try
        (io/move-file src (temp-path "dest.edn"))
        (is false "Should have thrown")
        (catch clojure.lang.ExceptionInfo e
          (is (= :not-found (:type (ex-data e))))
          (is (= src (:path (ex-data e)))))))))

;; =============================================================================
;; list-edn-files Tests
;; =============================================================================

(deftest list-edn-files-empty-dir-test
  (testing "Returns empty vector for empty directory"
    (let [dir (temp-path "empty-dir")]
      (fs/create-dirs dir)
      (is (= [] (io/list-edn-files dir))))))

(deftest list-edn-files-nonexistent-dir-test
  (testing "Returns empty vector for non-existent directory"
    (is (= [] (io/list-edn-files (temp-path "nonexistent"))))))

(deftest list-edn-files-basic-test
  (testing "Lists .edn files in directory"
    (let [dir (temp-path "edn-dir")]
      (fs/create-dirs dir)
      (spit (str (fs/path dir "a.edn")) "a")
      (spit (str (fs/path dir "b.edn")) "b")
      (spit (str (fs/path dir "c.txt")) "c")  ; not .edn
      (let [result (io/list-edn-files dir)]
        (is (= 2 (count result)))
        (is (every? #(clojure.string/ends-with? % ".edn") result))))))

(deftest list-edn-files-sorted-test
  (testing "Returns files in sorted order"
    (let [dir (temp-path "sorted-dir")]
      (fs/create-dirs dir)
      (spit (str (fs/path dir "z.edn")) "z")
      (spit (str (fs/path dir "a.edn")) "a")
      (spit (str (fs/path dir "m.edn")) "m")
      (let [result (io/list-edn-files dir)
            filenames (map #(fs/file-name %) result)]
        (is (= ["a.edn" "m.edn" "z.edn"] filenames))))))

(deftest list-edn-files-non-recursive-test
  (testing "Does not recurse by default"
    (let [dir (temp-path "parent")]
      (fs/create-dirs (str (fs/path dir "child")))
      (spit (str (fs/path dir "parent.edn")) "p")
      (spit (str (fs/path dir "child" "child.edn")) "c")
      (let [result (io/list-edn-files dir)]
        (is (= 1 (count result)))
        (is (clojure.string/ends-with? (first result) "parent.edn"))))))

(deftest list-edn-files-recursive-test
  (testing "Recurses when :recursive true"
    (let [dir (temp-path "recurse")]
      (fs/create-dirs (str (fs/path dir "a")))
      (fs/create-dirs (str (fs/path dir "a" "b")))
      (spit (str (fs/path dir "root.edn")) "r")
      (spit (str (fs/path dir "a" "level1.edn")) "1")
      (spit (str (fs/path dir "a" "b" "level2.edn")) "2")
      (let [result (io/list-edn-files dir :recursive true)]
        (is (= 3 (count result)))))))

;; =============================================================================
;; file-exists? Tests
;; =============================================================================

(deftest file-exists-true-test
  (testing "Returns true for existing file"
    (let [path (temp-path "exists.txt")]
      (spit path "content")
      (is (true? (io/file-exists? path))))))

(deftest file-exists-false-test
  (testing "Returns false for non-existent file"
    (is (false? (io/file-exists? (temp-path "nope.txt"))))))

(deftest file-exists-directory-test
  (testing "Returns false for directory"
    (let [dir (temp-path "a-dir")]
      (fs/create-dirs dir)
      (is (false? (io/file-exists? dir))))))

;; =============================================================================
;; dir-exists? Tests
;; =============================================================================

(deftest dir-exists-true-test
  (testing "Returns true for existing directory"
    (let [dir (temp-path "a-directory")]
      (fs/create-dirs dir)
      (is (true? (io/dir-exists? dir))))))

(deftest dir-exists-false-test
  (testing "Returns false for non-existent directory"
    (is (false? (io/dir-exists? (temp-path "no-such-dir"))))))

(deftest dir-exists-file-test
  (testing "Returns false for file"
    (let [path (temp-path "file.txt")]
      (spit path "content")
      (is (false? (io/dir-exists? path))))))

;; =============================================================================
;; ensure-dir Tests
;; =============================================================================

(deftest ensure-dir-creates-test
  (testing "Creates directory if it doesn't exist"
    (let [dir (temp-path "new-dir")]
      (is (not (fs/exists? dir)))
      (io/ensure-dir dir)
      (is (fs/directory? dir)))))

(deftest ensure-dir-nested-test
  (testing "Creates nested directories"
    (let [dir (temp-path "a" "b" "c")]
      (io/ensure-dir dir)
      (is (fs/directory? dir)))))

(deftest ensure-dir-exists-test
  (testing "Does nothing if directory already exists"
    (let [dir (temp-path "existing")]
      (fs/create-dirs dir)
      (spit (str (fs/path dir "file.txt")) "content")
      (io/ensure-dir dir)
      (is (fs/exists? (str (fs/path dir "file.txt")))))))

(deftest ensure-dir-returns-path-test
  (testing "Returns the path"
    (let [dir (temp-path "return-test")]
      (is (= dir (io/ensure-dir dir))))))
