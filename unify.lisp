;;
;; Constants
;;
;; Indicates pattern match failure
(defconstant fail nil)
;;
;; Indicates pattern match success, with no variables
(defconstant no-bindings '((t . t)))

  
;;
;; UNIFY
;;
(defun unify (x y &optional (bindings no-bindings))
  (cond ((eq bindings fail) fail)
        ((eql x y) bindings)
        ((variable-p x) (unify-variable x y bindings))
        ((variable-p y) (unify-variable y x bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
                (unify (first x) (first y) bindings)))
        (t fail)))

;;
;; UNIFIER
;;
(defun unifier (x y)
  (subst-bindings (unify x y) x))

;;
;; 
;;
(defun subst-bindings (bindings x)
  (cond ((eq bindings fail) fail)
        ((eq bindings no-bindings) x)
        ((and (variable-p x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

;;
;; UNIFY-VARIABLE
;;
(defun unify-variable (var x bindings)
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable-p x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        (t (extend-bindings var x bindings))))

;;
;; VARIABLE-P
;;
(defun variable-p (x)
  (and (symbolp x) (equal (char (symbol-name x) 0) #\?)))

;;
;; GET-BINDING
;; Find a (variable . value) pair in a binding list.
;; In  <object> <association list>
;; Out <cons>
;;
(defun get-binding (var bindings)
  (assoc var bindings))

;; *
;; LOOKUP
;; 
(defun lookup (var bindings)
  (binding-val (get-binding var bindings)))

;;
;; BINDING-VAL
;;
(defun binding-val (binding)
  (cdr binding))

;;
;; EXTEND-BINDINGS
;;
(defun extend-bindings (var val bindings)
  (cons (cons var val)
        (if (eq bindings no-bindings)
            nil
          bindings)))

;;
;; MATCH-VARIABLE
;; p158
;;
(defun match-variable (var input bindings)
  (let ((binding (get-binding var bindings)))
    (cond ((not binding) (extend-bindings var input bindings))
          ((equal input (binding-val binding)) bindings)
          (t fail))))

;;
;; REUSE-CONS
;; See p333 - Efficiency issues
;;
(defun reuse-cons (x y x-y)
  (if (and (eql x (car x-y)) (eql y (cdr x-y)))
      x-y
    (cons x y)))
