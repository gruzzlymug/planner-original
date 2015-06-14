;;===
;; DEBUG FRAMEWORK
;;===
;;
;; Holds active debug ids
;;
(defvar *dbg-ids* nil "Identifiers used by dbg")

;;
;; Print under proper circumstances
;;
(defun dbg (id format-string &rest args)
  "Print debugging info if (DEBUG ID) has been specified."
  (when (member id *dbg-ids*)
    (fresh-line *debug-io*)
    (apply #'format t format-string args)))

;;
;;
;;
(defun dbg-on (&rest ids)
  "Start dbg output on the given ids."
  (setf *dbg-ids* (union ids *dbg-ids*)))

;;
;;
;;
(defun dbg-off (&rest ids)
  "Stop dbg output on the ids. With no ids, stop on all."
  (setf *dbg-ids* (if (null ids) nil
                    (set-difference *dbg-ids* ids))))


;;
;; DBG-INDENT
;;
(defun dbg-indent (id indent format-string &rest args)
  (when (member id *dbg-ids*)
    (fresh-line *debug-io*)
    (dotimes (i indent) (princ "  " *debug-io*))
    (apply #'format *debug-io* format-string args)))