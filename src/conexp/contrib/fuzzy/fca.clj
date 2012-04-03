;; Copyright (c) Daniel Borchmann. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file LICENSE at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns conexp.contrib.fuzzy.fca
  (:use conexp.main
        [conexp.contrib.fuzzy sets logics]))

(ns-doc "Basic definitions for Fuzzy FCA")

;;;

(deftype Fuzzy-Context [values objects attributes incidence]
    Object
  (equals [this other]
    (generic-equals [this other] Fuzzy-Context [values objects attributes incidence]))
  (hashCode [this]
    (hash-combine-hash Fuzzy-Context values objects attributes incidence))
  ;;
  conexp.fca.contexts/Context
  (objects [this] objects)
  (attributes [this] attributes)
  (incidence [this] incidence))

(defn values
  "Returns all possible truth values for the given Fuzzy-Context."
  [^Fuzzy-Context fctx]
  (.values fctx))

(defn- mv->fuzzy-context-nc
  "Converts a many-valued-context to a fuzzy context, without checking."
  [values mv-ctx]
  (Fuzzy-Context. values (objects mv-ctx) (attributes mv-ctx) (make-fuzzy-set (incidence mv-ctx))))

(defmethod print-method Fuzzy-Context
  [ctx out]
  (let [^java.io.Writer out out]
    (.write out (str "Fuzzy-Context\n with values " (values ctx) "\n\n"))
    (.write out (mv-context-to-string (make-mv-context (objects ctx)
                                                       (attributes ctx)
                                                       (fn [a b] ((incidence ctx) [a b])))))))

;;;

(defmulti make-fuzzy-context
  "Creates a fuzzy context from the given attributes. A fuzzy context
  is nothing else than a Many-Valued Context with real entries between
  0 and 1."
  {:arglists '([values objects attributes incidence])}
  (fn [& args]
    (vec (map clojure-type args))))

(defmethod make-fuzzy-context [clojure-coll clojure-coll clojure-coll clojure-fn]
  [values objects attributes truth-function]
  (let [mv-ctx (make-mv-context (set objects)
                                (set attributes)
                                truth-function)]
    (when-not (forall [v (vals (incidence mv-ctx))] (and (number? v) (<= 0 v 1)))
      (illegal-argument "Given function does not return real values between 0 and 1."))
    (mv->fuzzy-context-nc values mv-ctx)))

(defmethod make-fuzzy-context [clojure-coll clojure-coll clojure-coll clojure-coll]
  [values objects attributes triples]
  (let [mv-ctx (make-mv-context-from-matrix objects attributes triples)]
    (when-not (forall [v (vals (incidence mv-ctx))] (and (number? v) (<= 0 v 1)))
      (illegal-argument "Given value table does not consist of real values between 0 and 1."))
    (mv->fuzzy-context-nc values mv-ctx)))

(defn make-fuzzy-context-from-matrix
  "Creates a fuzzy context from the given (number of) objects, (number
  of) attributes and the value matrix, which must contain only real
  values between 0 and 1."
  [values objects attributes matrix]
  (make-fuzzy-context values objects attributes matrix))

;;;

(defn fuzzy-object-derivation
  "Computes the fuzzy derivation of the fuzzy set C of objects in the given context, using hedge if
  given."
  ([context C]
     (fuzzy-object-derivation context C identity))
  ([context C hedge]
     (let [inz (incidence context),
           C   (make-fuzzy-set C)]
       (make-fuzzy-set (map-by-fn (fn [m]
                                    (reduce (fn [a g]
                                              (f-and a (f-impl (hedge (C g)) (inz [g m]))))
                                            1
                                            (objects context)))
                                  (attributes context))))))

(defalias fuzzy-oprime fuzzy-object-derivation)

(defn fuzzy-attribute-derivation
  "Computes the fuzzy derivation of the fuzzy set D of attributes in the given context."
  [context D]
  (let [inz (incidence context),
        D   (make-fuzzy-set D)]
    (make-fuzzy-set (map-by-fn (fn [g]
                                 (reduce (fn [a m]
                                           (f-and a (f-impl (D m) (inz [g m]))))
                                         1
                                         (attributes context)))
                               (objects context)))))

(defalias fuzzy-aprime fuzzy-attribute-derivation)

(defn doubly-scale-fuzzy-context
  "Returns the doubly scaled formal context for the given fuzzy
  context ctx."
  [ctx]
  (let [inz  (incidence ctx),
        vals (-> (set (vals inz)) (disj 0)),
        objs (set-of [g ny]
                     [g (objects ctx),
                      ny vals]),
        atts (set-of [m lambda]
                     [m (attributes ctx),
                      lambda vals]),
        inci  (set-of [[g ny] [m lambda]]
                      [[g ny] objs,
                       [m lambda] atts,
                       :when (<= (f-star ny lambda)
                                 (inz [g m]))])]
    (make-context objs atts inci)))

;;; Hedges

(defn globalization
  "Implements globalization."
  [x]
  (if (= x 1) 1 0))

(defn validity
  "Returns the degree to which the implication A ==> B is true in the
  given fuzzy-context. A and B are fuzzy subsets of the attributes of
  fuzzy-context."
  ([fuzzy-context A B]
     (validity fuzzy-context A B identity))
  ([fuzzy-context A B hedge]
     (subsethood (make-fuzzy-set B)
                 (fuzzy-oprime fuzzy-context
                               (fuzzy-aprime fuzzy-context
                                             (make-fuzzy-set A))
                               hedge))))

;;; Next-Closure to compute fuzzy concepts

(defn- pairs->fuzzy-set
  "Does what it says."
  [pairs]
  (-> (reduce! (fn [map [x v]]
                 (if (or (not (contains? map x))
                         (< (map x) v))
                   (assoc! map x v)
                   map))
               {}
               pairs)
      make-fuzzy-set))

(defn- fuzzy-set->pairs
  "Does what it says."
  [values fset]
  (seq (set-of [x v] | [x a] fset, v values :when (<= v a))))



;;;

;;; TODO:
;;;  - Compute fuzzy concepts
;;;  - attribute exploration?
;;;  - non-redundant basis of implications

;;;

nil
