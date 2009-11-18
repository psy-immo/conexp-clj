(ns conexp.contrib.doc
  (:use [conexp :only (*conexp-namespaces*)]
	[clojure.contrib.duck-streams :only (with-out-writer)]))


(defn public-api
  "Returns a map of public functions of namespaces to their
  corresponding documentation."
  [ns]
  (let [ns (find-ns ns)]
    (map (fn [[function var]]
	   [function (str (:arglists ^var)
			  "\n\n"
			  (:doc ^var))])
	 (filter (fn [[_ v]]
		   (= (:ns (meta v)) ns))
		 (ns-map ns)))))

(defn tex-escape
  "Escapes special characters for \\TeX."
  [string]
  (let [sb (StringBuilder.)
	string (str string)]
    (doseq [c string]
      (cond
	(#{\_,\&,\%,\#} c)
	(.append sb (str \\ c))
	(#{\^} c)
	(.append sb "\\verb+^+")
	:else
	(.append sb c)))
    (str sb)))

(defn public-api-as-tex
  "Returns output suitable for \\TeX describing the public apis of the
  given namespaces with their corresponding documentations."
  [& namespaces]
  (with-out-str
    (doseq [ns namespaces]
      (let [api (sort (public-api ns))]
	(println (str "\\section{" (tex-escape ns) "}"))
	(println "\\begin{description}")
	(doseq [[fn doc] api]
	  (println (str "  \\item[" (tex-escape fn) "]"))
	  (println (tex-escape doc))
	  (println))
	(println "\\end{description}"))
      (println))))

(defn public-api-to-file
  "Prints out public api to file for external usage."
  [file & namespaces]
  (with-out-writer file
    (print (apply public-api-as-tex namespaces))))

(defn conexp-api
  "Prints conexp-clj api to file."
  [file]
  (apply public-api-to-file file *conexp-namespaces*))

nil