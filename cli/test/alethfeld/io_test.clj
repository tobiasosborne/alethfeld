(ns alethfeld.io-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [clojure.java.io :as jio]
            [alethfeld.io :as io]
            [alethfeld.fixtures :as f]))

(def ^:dynamic *temp-dir* nil)

(defn temp-dir-fixture [f]
  (let [dir (java.io.File/createTempFile "alethfeld-test-" "")]
    (.delete dir)
    (.mkdirs dir)
    (binding [*temp-dir* dir]
      (try
        (f)
        (finally
          (doseq [file (file-seq dir)]
            (.delete file)))))))

(use-fixtures :each temp-dir-fixture)

(deftest read-edn-test
  (testing "Read valid EDN file"
    (let [path (str *temp-dir* "/test.edn")
          data {:foo "bar" :baz 123}]
      (spit path (pr-str data))
      (let [result (io/read-edn path)]
        (is (:ok result))
        (is (= data (:ok result))))))

  (testing "Read missing file returns error"
    (let [result (io/read-edn "/nonexistent/path/file.edn")]
      (is (:error result))
      (is (re-find #"not found" (:error result)))))

  (testing "Read empty file returns error"
    (let [path (str *temp-dir* "/empty.edn")]
      (spit path "")
      (let [result (io/read-edn path)]
        (is (:error result))
        (is (re-find #"[Ee]mpty" (:error result))))))

  (testing "Read malformed EDN returns error"
    (let [path (str *temp-dir* "/bad.edn")]
      (spit path "{:broken")
      (let [result (io/read-edn path)]
        (is (:error result))
        (is (re-find #"parse" (:error result)))))))

(deftest write-edn-test
  (testing "Write and read back preserves data"
    (let [path (str *temp-dir* "/roundtrip.edn")
          data f/minimal-valid-graph]
      (let [write-result (io/write-edn-atomic path data)]
        (is (:ok write-result)))
      (let [read-result (io/read-edn path)]
        (is (:ok read-result))
        (is (= data (:ok read-result))))))

  (testing "Write creates parent directories"
    (let [path (str *temp-dir* "/subdir/test.edn")
          data {:test true}]
      (.mkdirs (jio/file *temp-dir* "subdir"))
      (let [result (io/write-edn-atomic path data)]
        (is (:ok result))))))

(deftest format-edn-test
  (testing "Format produces readable EDN"
    (let [data {:a 1 :b [2 3]}
          formatted (io/format-edn data)]
      (is (string? formatted))
      (is (= data (read-string formatted)))))

  (testing "Compact format produces readable EDN"
    (let [data {:a 1 :b [2 3]}
          formatted (io/format-edn-compact data)]
      (is (string? formatted))
      (is (= data (read-string formatted)))))

  (testing "Pretty format produces readable EDN"
    (let [data {:a 1 :b [2 3]}
          formatted (io/format-edn-pretty data)]
      (is (string? formatted))
      (is (= data (read-string formatted)))))

  (testing "Compact format is smaller than pretty format"
    (let [data {:foo "bar" :nested {:a 1 :b 2 :c [1 2 3 4 5]}}
          compact (io/format-edn-compact data)
          pretty (io/format-edn-pretty data)]
      (is (< (count compact) (count pretty)))))

  (testing "Both formats parse identically"
    (let [data f/minimal-valid-graph
          compact (io/format-edn-compact data)
          pretty (io/format-edn-pretty data)]
      (is (= (read-string compact) (read-string pretty))))))
