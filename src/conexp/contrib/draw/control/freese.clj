;; Copyright (c) Daniel Borchmann. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file LICENSE at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns conexp.contrib.draw.control.freese
  (:use conexp.layouts.base
        conexp.layouts.freese
        conexp.contrib.draw.control.util
        conexp.contrib.draw.scenes
        conexp.contrib.draw.scene-layouts
        conexp.contrib.gui.util)
  (:import [javax.swing JButton JSpinner JFrame]
           [java.awt.event WindowEvent WindowAdapter]))

;;; Freese layout

(defn freese
  "Installs Freese Layout control."
  [frame scn buttons]
  (let [^JButton btn    (make-button buttons "Freese"),
        ^JSpinner spn   (make-spinner buttons 0 (* 2 Math/PI) 0 0.01),
        layout          (interactive-freese-layout (lattice (get-layout-from-scene scn))),
        get-value       #(.getValue spn),
        ^JButton rotate (make-button buttons "Rotate"),
        rotate-thread   (atom nil),
        start-rotate    #(when-not @rotate-thread
                           (update-layout-of-scene scn (layout (get-value)))
                           (fit-scene-to-layout scn)
                           (reset! rotate-thread
                                   (Thread. (fn []
                                              (doseq [angle (drop-while (let [y (get-value)]
                                                                          (fn [x] (<= x y)))
                                                                        (cycle (range 0 (* 2 Math/PI) 0.05))),
                                                      :while @rotate-thread]
                                                (Thread/sleep 50)
                                                (.setValue spn angle)))))
                           (.start ^Thread @rotate-thread)),
        stop-rotate     #(when @rotate-thread
                           (.stop ^Thread @rotate-thread)
                           (reset! rotate-thread nil))]
    (with-action-on btn
      (update-layout-of-scene scn (layout (get-value)))
      (fit-scene-to-layout scn))
    (with-change-on spn
      (update-layout-of-scene scn (layout (get-value))))
    (with-action-on rotate
      (if @rotate-thread
        (stop-rotate)
        (start-rotate)))
    (.addWindowListener ^JFrame frame
                        (proxy [WindowAdapter] []
                          (windowIconified [win-evt]
                            (stop-rotate))
                          (windowClosed [win-evt]
                            (stop-rotate))))))

;;;

nil
