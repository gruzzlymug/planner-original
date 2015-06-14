;;===
;;
;; Kevin Guran
;; CSC 380 - Final Project
;; 9 Mar 2004
;;
;; Implementation of GRAPHPLAN algorithm
;;
;; Algorithm based on the original paper by A. Blum and M. Furst
;;   and AIMA by S. Russell and P. Norvig.
;; Data structures based on C HEADER by A. Blum and M. Furst.
;; Unification code from PAIP by P. Norvig.
;;
;; TODO
;; ** Make a sequence diagram for the GPS algorithm
;; ** Make an outline of the improvements from the book
;; ** Do state lists need to be sets?
;;
;; For structure stuff see Norvig, AIP p115
;;
;;===
;;
;; Global variables
;;
(defvar *state* nil)       ; initially the start state
(defvar *goals* nil)       ; where we want to be
(defvar *ops* nil)         ; ways we can get there
(defvar *actors* nil)      ; who we are operating on
(defvar *props-ht* nil)
(defvar *actions-ht* nil)
 
;;
;; Operator
;;
(defstruct op
  (operator nil)
  (params nil)
  (preconds nil)
  (add-list nil)
  (del-list nil))

;;
;; Proposition (state) or Action Levels for the planning graph
;; ** this is not used
(defstruct level
  (level 0))

;;
;; Vertex Key - to map to a vertex in a hash table 
;; Since lists can't be used as keys, this struct will hold them instead.
;;
(defstruct vertex-key
  (name nil))

;;
;; Vertex for the planning graph
;; Using a unique structure instance for a key - possible efficiency issue.
;;
(defstruct vertex
  (name nil)
  (hash nil)
  (in-edges nil)
  (out-edges nil)
  (del-edges nil)
  (exclusive nil)
  (is-noop nil))

;;
;; GP = graphPLAN
;; Top level function
;;
(defun gp ()
  (load-ops)
  (load-facts)
  (setq max-time (create-graph))
  (cond ((null max-time) (end-failure))
        (t (end-success)))
  max-time)

;;
;; LOAD-OPS
;;
(defun load-ops (&optional (filepath "c:\\projects\\csc380\\project\\block_ops.txt"))
  (format t "load-ops~%")
  (setf *ops* nil)
  (setf *actions-ht* (make-hash-table))
  (file-reader filepath))

;;
;; LOAD-FACTS
;;
(defun load-facts (&optional (filepath "c:\\projects\\csc380\\project\\block_facts.txt"))
  (format t "load-facts~%")
  (setf *props-ht* (make-hash-table))
  (file-reader filepath))

;;----------------------------------------------------------------------------
;;----------------------------------------------------------------------------

;;===
;; GRAPH CONSTRUCTION
;;===
;;
;; CREATE-GRAPH
;; Creates the first state level and starts the planning graph creation.
;;
(defun create-graph (&optional (state *state*))
  (format t "create-graph~%")
  (format t "create-prop-level ~a~%" 1)
  (let ((initial-prop-level (make-prop-vert state)))
    (create-level-pair initial-prop-level nil 1)))

;;
;; CREATE-LEVEL-PAIR
;; Recursively creates level pairs until goals exist non-exclusively in
;; prop-level or when the graph levels off.
;; Returns the last state reached for whichever condition occurs.
;; ** Mutexes - should prop-ex-check be put somewhere else?
;;
(defun create-level-pair (prop-level last-prop-level level-number)
  (cond ((unless (or (leveled-off-p prop-level last-prop-level)
                     (goals-exist-p prop-level))
           (setf action-level (create-action-level *ops* prop-level level-number))
           (connect-pa prop-level action-level)
           (clean-in-edges action-level)
           (setf new-prop-level (create-prop-level action-level (+ 1 level-number)))
           (connect-ap action-level new-prop-level)
           (clean-out-edges action-level)
           (clean-del-edges action-level)
           (prop-ex-check new-prop-level new-prop-level)
           (append (list prop-level action-level)
                   (create-level-pair new-prop-level prop-level (+ 1 level-number)))))
        (t (list prop-level))))

;;
;; LEVELED-OFF-P
;; Checks two vertex-key-name lists against each other.
;; If they contain the same names, then leveled-off-p is true.
;; ** would want to check lists as well, if necessary. Not sure if
;;    names would stay the same while in, out & del lists change.
;;
(defun leveled-off-p (prop-level last-prop-level)
  (let ((prop-names (mapcar #'vertex-name prop-level))
        (last-prop-names (mapcar #'vertex-name last-prop-level)))
    (and (subsetp prop-names last-prop-names)
         (subsetp last-prop-names prop-names))))

;;
;;
;;
(defun goals-exist-p (prop-level)
  nil)

;;
;; CLEAN-EDGES
;; The action vertices are created with each connecting edge represented as a list.
;; The lists are later replaced with the hash keys of the vertices they represent.
;; These functions clean the lists out of edge lists.
;; This is part of the 2 step process of creation and connection of levels.
;;
;; ** These 3 could probably be consolidated with macro.
;;
(defun clean-in-edges (level)
    (mapc #'(lambda (v) (setf (vertex-in-edges v) (remove-if-not #'vertex-key-p (vertex-in-edges v)))) level))

(defun clean-out-edges (level)
    (mapc #'(lambda (v) (setf (vertex-out-edges v) (remove-if-not #'vertex-key-p (vertex-out-edges v)))) level))

(defun clean-del-edges (level)
    (mapc #'(lambda (v) (setf (vertex-del-edges v) (remove-if-not #'vertex-key-p (vertex-del-edges v)))) level))


;;===
;; PROPOSITION LEVEL CONSTRUCTION
;; The first proposition level is a special case
;;===
;;
;; CREATE-PROP-LEVEL
;; A prop-level is a list of proposition vertices
;;
(defun create-prop-level (action-level level-number)
  (format t "create-prop-level ~a~%" level-number)
  (let* ((state (remove-duplicates (process-actions action-level) :test #'equal))
         (prop-level (make-prop-vert state)))
    (dbg :state "State: ~a~%" state)
    prop-level))

;;
;; PROCESS-ACTIONS
;; ** Make sure that edges are connected properly - Section 3.1 paragraph 2
;; Gets all the states from all of the actions
;;
(defun process-actions (action-verts)
  (cond ((consp action-verts)
         (append (vertex-out-edges (car action-verts))
                 (process-actions (cdr action-verts))))))

;;
;; MAKE-PROP-VERT
;; Makes a list of proposition vertices, actually
;;
(defun make-prop-vert (props &optional (verts nil))
  (cond ((not (null props))
         (let* ((name (car props))
                (k (make-vertex-key :name name))
                (v (make-vertex :name name :hash k)))
           (dbg :gp "Making prop-vert: ~a~%" name)
           (setf (gethash k *props-ht*) v)
           (make-prop-vert (cdr props) (append verts (list v)))))
        (t verts)))

;;
;; PROP-EX-CHECK
;; Exclusivity check - See [1: Section 3.1 & maybe 2.2] 
;; Two propositions are exclusive if all ways of generating the first are exclusive of
;; all ways of generating the second.
;; Possible to go 1 way down the list with 2-way excl inserts...figure it out
;; ** fn form is exactly the same as the one for actions...
;;
(defun prop-ex-check (props other-props)
  (cond ((not (null props))
         (prop-ex-chk-2 (car props) (remove (car props) other-props))
         (prop-ex-check (cdr props) other-props))))

;;
;; PROP-EX-CHK-2
;; Checks a proposition against each proposition in a list of proposition
;; Adds to the 'propositions-i-am-exclusive-of' list, if req'd
;; ** would benefit from a hash table implementation, too.
;;
(defun prop-ex-chk-2 (prop other-props)
  (cond ((not (null other-props))
         (dbg :p-ex "Ex-Check: ~a vs ~a~%" (vertex-name prop) (vertex-name (car other-props)))
         (if (prop-exclusive-p prop (car other-props))
             (push (vertex-hash (car other-props)) (vertex-exclusive prop)))
         (prop-ex-chk-2 prop (cdr other-props) ))
        (t nil)))

;;
;; PROP-EXCLUSIVE-P
;; All ways of generating one prop are exclusive of the ways of generating
;; the other prop
;;
(defun prop-exclusive-p (prop other-prop &optional (ex-1 nil) (ex-2 nil))
  (let* ((ways-1 (vertex-in-edges prop))
         (generate-1 (mapcar #'vertex-key-name ways-1))
         (exclusive-1 (mapcar #'vertex-key-name (www ways-1)))
         (ways-2 (vertex-in-edges other-prop))
         (generate-2 (mapcar #'vertex-key-name ways-2))
         (exclusive-2 (mapcar #'vertex-key-name (www ways-2)))
         (ex-p (not (and (set-difference generate-1 exclusive-2)
                         (set-difference generate-2 exclusive-1)))))
    (dbg :p-ex "  g-p1: ~a" generate-1)
    (dbg :p-ex "  e-p2: ~a" exclusive-1)
    (dbg :p-ex "  g-p2: ~a" generate-2)
    (dbg :p-ex "  e-p1: ~a" exclusive-1)
    (dbg :p-ex "  excl? ~a" ex-p)
    ex-p))

;;
;; Returns a list of all actions...
;;
(defun www (x)
  (cond ((consp x)
         (append (vertex-exclusive (gethash (car x) *actions-ht*))
                 (www (cdr x))))))

;;===
;; ACTION LEVEL CONSTRUCTION
;;===
;;
;; CREATE-ACTION-LEVEL
;; Find a list of all operators that can be supplied in the current state
;; then...
;;
(defun create-action-level (ops prop-level level-number)
  (format t "create-action-level ~a~%" level-number)
  (let* ((current-state (mapcar #'(lambda (v) (vertex-name v)) prop-level))
         (applicable-ops (process-ops ops prop-level))
         (no-ops (process-props prop-level))
         (all-ops (append applicable-ops no-ops)))
    (excl-check all-ops all-ops)
    all-ops))

;;
;; PROCESS-OPS
;; For each operator, find the full list of actor permutations.
;; Next, determine which ones can be applied given the current state.
;; Returns a list of vertices - instantiations of operators
;;
(defun process-ops (ops prop-level)
  (cond ((consp ops)
         (dbg :gp "Processing: ~a~%" (op-operator (car ops)))
         (let* ((op (car ops))
                (perms (bind-params op)))
           (append (if (not (null perms))
                       (make-action-vert op (find-valid-preconds (op-preconds op) perms prop-level) nil))
                   (process-ops (cdr ops) prop-level))))))

;;
;; MAKE-ACTION-VERT
;; For each valid permutation, create a vertex for this operator 
;; and put it in the hash table.
;; 
;; ** Based on the current state
;;
(defun make-action-vert (op valid-perms &optional (verts nil))
  (cond ((not (null valid-perms))
         (let* ((perm (car valid-perms))
                (inst (subst-bindings perm (op-params op)))
                (name (cons (op-operator op) (mapcar #'car inst)))
                (in-edges (subst-bindings perm (op-preconds op)))
                (out-edges (subst-bindings perm (op-add-list op)))
                (del-edges (subst-bindings perm (op-del-list op)))
                (k (make-vertex-key :name name))
                (v (make-vertex :name name :hash k :in-edges in-edges
                                :out-edges out-edges :del-edges del-edges)))
           (dbg :gp "Making action-vert: ~a~%" name)
           (dbg :gp "  in-edges : ~a~%" in-edges)
           (dbg :gp "  out-edges: ~a~%" out-edges)
           (dbg :gp "  del-edges: ~a~%" del-edges)
           (setf (gethash k *actions-ht*) v)
           (make-action-vert op (cdr valid-perms) (append verts (list v)))))
        (t verts)))

;;
;; PROCESS-PROPS
;; This is here primarily for consistency with the action level api.
;;
(defun process-props (prop-level)
  (let ((current-state (mapcar #'(lambda (v) (vertex-name v)) prop-level)))
    (make-noop-vert current-state)))

;;
;; MAKE-NOOP-VERT
;; Create the vertex and put it in the hash table.
;; No-ops never conflict with other vertices in their level, but
;; others may conflict with them.
;;
(defun make-noop-vert (props &optional (verts nil))
  (cond ((not (null props))
         (let* ((prop (car props))
                (k (make-vertex-key :name prop))
                (v (make-vertex :name prop :hash k :is-noop t
                                :in-edges (list prop) :out-edges (list prop))))
           (setf (gethash k *actions-ht*) v)
           (make-noop-vert (cdr props) (append verts (list v)))))
        (t verts)))

;;
;; EXCL-CHECK
;; Exclusivity check - See [1: Section 2.2] 
;; Possible to go 1 way down the list with 2-way excl inserts...figure it out
;;
(defun excl-check (actions other-actions)
  (cond ((not (null actions))
         (ex-chk-2 (car actions) (remove (car actions) other-actions))
         (excl-check (cdr actions) other-actions))))

;;
;; EX-CHK-2
;; Checks an action against each action in a list of actions
;; Adds to the 'actions-i-am-exclusive-of' list, if necessary
;; Adds reciprocal exclusive entry to no-op actions (which have no delete edges)
;;
(defun ex-chk-2 (action other-actions &optional (exclusive nil))
  (cond ((not (null other-actions))
         (let ((suspect (car other-actions)))
           (dbg :a-ex "Ex-Check: ~a vs ~a~%" (vertex-name action) (vertex-name suspect))
           (if (act-interferes-p action suspect)
               (progn
                 (push (vertex-hash suspect) (vertex-exclusive action))
                 (if (vertex-is-noop suspect)
                     (push (vertex-hash action) (vertex-exclusive suspect)))))
           (ex-chk-2 action (cdr other-actions) (append (vertex-name (car other-actions)) exclusive))))
        (t exclusive)))

;;
;; ACT-INTERFERES-P
;; One action deletes the preconditions of another, which
;; results in the creation of mutex links between the two.
;;
(defun act-interferes-p (a b)
  (let* ((del-edges (vertex-del-edges a))
         (in-edges (vertex-in-edges b))
         (interferes (intersection del-edges in-edges :test #'equal)))
;    (dbg :gp "  act-int ~a~%" interferes)
    interferes))

;;
;; ACT-COMPETING-NEEDS-P
;; A precondition for one action is mutex of a precondition for
;; the other.
;; This prevents the action from being instantiated.
;;
(defun act-competing-needs-p (a b)
;  (dbg :gp "  comp-needs~%")
  )

;;===
;; CONNECT PROPOSITION LEVEL TO ACTION LEVEL
;;===
;;
;; CONNECT-PA
;; Connect a proposition level to an action level
;; ** Is there a better way to save prop-level? Some type of idiom perhaps?
;;
(defun connect-pa (prop-level action-level)
  (cond ((and (consp prop-level)
              (consp action-level))
         (setf pl2 prop-level)
         (connect-to-action prop-level (car action-level))
         (connect-pa pl2 (cdr action-level)))))

;;
;; CONNECT-TO-ACTION
;; Test all props against an action and add edges between them
;; ** consider a predicate for this...
;;
(defun connect-to-action (prop-level action)
  (let ((prop (car prop-level)))
    (cond ((consp prop-level)
           (if (member (vertex-name prop) (vertex-in-edges action) :test #'equal)
               (progn
                 (add-out-edge prop action)
                 (add-in-edge action prop)))
           (connect-to-action (cdr prop-level) action)))))

;;===
;; CONNECT ACTION LEVEL TO PROPOSITION LEVEL
;;===
;;
;; CONNECT-AP
;; Connect an action level to a proposition level
;;
(defun connect-ap (action-level prop-level)
  (cond ((and (consp action-level)
              (consp prop-level))
         (setf al2 action-level)
         (connect-to-prop action-level (car prop-level))
         (connect-ap al2 (cdr prop-level)))))

;;
;; CONNECT-TO-PROP
;; Test all actions against a proposition and add edges between them
;; ** add-*-edge fns are good candidates for refactoring
;;
(defun connect-to-prop (action-level prop)
  (let ((action (car action-level)))
    (cond ((consp action-level)
           (if (member (vertex-name prop) (vertex-out-edges action) :test #'equal)
               (progn
                 (add-out-edge action prop)
                 (add-in-edge prop action)))
           (if (member (vertex-name prop) (vertex-in-edges action) :test #'equal)
               (progn
                 (add-in-edge action prop)))
           (if (member (vertex-name prop) (vertex-del-edges action) :test #'equal)
               (progn
                 (add-del-edge action prop)))
           (connect-to-prop (cdr action-level) prop)))))

;;
;; ADD-IN-EDGE - These 3 should really just be one function (or macro)
;;
(defun add-in-edge (to from)
  (let ((hash (vertex-hash from)))
    (dbg :graph "In-Edge: connecting ~a to ~a~%" (vertex-key-name from) (vertex-name to))
    (push hash (vertex-in-edges to))))

;;
;; ADD-OUT-EDGE
;;
(defun add-out-edge (from to)
  (let ((hash (vertex-hash to)))
    (dbg :graph "Out-Edge: connecting ~a to ~a~%" (vertex-name from) hash)
    (push hash (vertex-out-edges from))))

;;
;; ADD-DEL-EDGE
;;
(defun add-del-edge (from to)
  (let ((hash (vertex-hash to)))
    (dbg :graph "Del-Edge: ~a removes ~a~%" (vertex-name from) hash)
    (push hash (vertex-del-edges from))))

;;----------------------------------------------------------------------------
;;----------------------------------------------------------------------------

;;
;; DO-PLAN
;;
(defun do-plan ()
  (format t "do-plan~%"))

;;
;; END-FAILURE
;;
(defun end-failure ()
  (format t "end-failure~%"))

;;
;; END-SUCCESS
;;
(defun end-success ()
  (format t "end-success~%"))

;;===
;; OPERATOR MANAGEMENT
;;===
;;
;; FIND-VALID-PRECONDS
;; Returns a list of parameter permutations that are applicable in the current state.
;;
(defun find-valid-preconds (preconds perms prop-level &optional (valid-perms nil))
  (cond ((not (null perms))
         (let* ((current-state (mapcar #'(lambda (v) (vertex-name v)) prop-level))
                (perm (car perms))
                (precond-inst (subst-bindings perm preconds)))
           (if (and (every #'(lambda (p) (member p current-state :test #'equal)) precond-inst)
                    (preconds-ex-p (mapcar #'(lambda (v) (if (member (vertex-name v) precond-inst :test #'equal) v)) prop-level)))
               (setf valid-perms (append valid-perms (list perm))))
           (find-valid-preconds preconds (cdr perms) prop-level valid-perms)))
        (t valid-perms)))


;;
;; PRECONDS-EX-P
;; Returns true if any precondition proposition is exclusive of another.
;; This is the 3rd mutex check.
;;
;; ** exclusive settings are too restrictive. returning true for now.
;;    this results in no actions being added. due to no-ops conflicting
;;    with actions that delete them.
;;    delete edges & no-ops might need to be treated together as a special case.
;;
(defun preconds-ex-p (p)
  (let ((preconds (remove-if #'null p)))
    (any-excl-check preconds preconds)
    t))

;;;;;;
;;
;; NOT WORKING YET (almost)
;;
;; Quickly assembled...
;;
;; ANY-EXCL-CHECK
;; Exclusivity check - See [1: Section 2.2] 
;; Possible to go 1 way down the list with 2-way excl inserts...figure it out
;; Make genenic for prop or action!
;;
(defun any-excl-check (actions other-actions)
  (cond ((not (null actions))
         (any-ex-chk-2 (car actions) (remove (car actions) other-actions))
         (any-excl-check (cdr actions) other-actions))))

;;
;; ANY-EX-CHK-2
;; Checks an action against each action in a list of actions
;; Adds to the 'actions-i-am-exclusive-of' list, if necessary
;; Adds reciprocal exclusive entry to no-op actions (which have no delete edges)
;;
(defun any-ex-chk-2 (action other-actions)
  (cond ((not (null other-actions))
         (let ((suspect (car other-actions)))
           (dbg :p-ex2 "Ex-Check2 : ~a vs ~a is ~a~%" (vertex-name action) (vertex-name suspect) (any-precond-interferes-p action suspect))
           (if (any-precond-interferes-p action suspect)
               t ; Found interference!
             (any-ex-chk-2 action (cdr other-actions)))))))

;;
;; ANY-PRECOND-INTERFERES-P (based on act-precond-interferes-p)
;; One action deletes the preconditions of another, which
;; results in the creation of mutex links between the two.
;;
(defun any-precond-interferes-p (a b)
  (let* ((a-exc-edges (mapcar #'vertex-key-name (vertex-exclusive a)))
         (a-name (vertex-name a))
         (b-exc-edges (mapcar #'vertex-key-name (vertex-exclusive b)))
         (b-name (vertex-name b))
         (interferes (or (member b-name a-exc-edges :test #'equal)
                         (member a-name b-exc-edges :test #'equal))))
    (dbg :p-ex2 "~a ~a ~a~%" b-name a-exc-edges (member b-name a-exc-edges :test #'equal))
    (dbg :p-ex2 "~a ~a ~a~%" a-name b-exc-edges (member a-name b-exc-edges :test #'equal))
    (dbg :p-ex2 "~a ~%" interferes)
    interferes))

;;;;;;

;;
;; BIND-PARAMS
;; For one operator, find all permutations of actors that satisfy
;; the input parameters.
;;
(defun bind-params (op)
  (let ((name (op-operator op))
        (params (op-params op)))
    (dbg :ops "Binding: ~a~%" name)
    (match-params params)))

;;
;; MATCH-PARAMS
;; Produce a list of parameter permutations given a list of types
;; and a list of typed actors.
;;
(defun match-params (params &optional (actors *actors*))
  (let* ((result (one-param (car params) actors))
         (leftover (cdr result)))
    (if (not (null result))
        (append (mapper (car result) (match-params (cdr params) *actors*))
                (if (not (null leftover))
                    (match-params params leftover))))))

;;
;; MAPPER
;; x is an atom or a list (*check this)
;; seq is a list of lists
;; this function prepends x to the front of every list in seq
;;
(defun mapper (x seq)
  (cond ((not (null seq))
         (append (list (append x (car seq)))
                 (if (not (null (cdr seq)))
                     (mapper x (cdr seq)))))
        (t (list x))))

;;
;; ONE-PARAM
;; if we have actors left to search 
;;   then take the first actor
;;   and unify it with the parameter
;;   assign the result to MATCH
;;   if (match found)
;;     then cons the binding with the rest of the actors
;;     and return that
;;   else
;;     search for a match in the rest of the actors
;; else
;;   return nil
;;
(defun one-param (param actors)
  (cond ((consp actors)
         (let* ((actor (car actors))
                (match (unify param actor)))
           (if (not (null match))
               (cons match (cdr actors))
             (one-param param (cdr actors)))))
        (t nil)))

;;===
;; I/O MANAGEMENT
;;===
;;
;; FILE-READER
;; Read a file of test data
;;
(defun file-reader (filepath)
  (setf s1 (open filepath :direction :input))
  (strips-reader s1)
  (close s1))

;;
;; STRIPS-READER
;; Take a stream and turn it into microSTRIPS structures
;;
(defun strips-reader (s-input)
  (cond ((not (listen s-input))
         'end-of-file-reached)
        (t
         (setf token (read s-input))
         (cond ((eq (car token) 'OPERATOR)
                (parse-op (cdr token)))
               ((eq (car token) 'START)
                (setf *state* (cdr token)))
               ((eq (car token) 'GOAL)
                (setq *goal* (cdr token)))
               ((eq (car token) 'ACTORS)
                (setf *actors* (cdr token))))
               (strips-reader s-input))))

;;
;; PARSE-OP
;; Reads an operator from a stream and adds it to the
;; global list of operators
;;
(defun parse-op (raw-op)
  (setq operator (car raw-op))
;  (print (list 'parsing operator))
  (setq params (cdr (second raw-op)))
  (setq preconds (cdr (third raw-op)))
  (setq add-list (cdr (fourth raw-op)))
  (setq del-list (cdr (fifth raw-op)))
  (add-op operator params preconds add-list del-list))

;;
;; ADD-OP
;; Adds an operator to the global operator list
;;
(defun add-op (operator params preconds add-list del-list)
  (push (make-op :operator operator :params params :preconds preconds
                 :add-list add-list :del-list del-list)
        *ops*))
