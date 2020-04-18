
(include-book "oslib/argv" :dir :system)

:set-state-ok t
:program

(defun car-cdr-gen (args var result)
    (cond ((null args) result)
        (t (car-cdr-gen (cdr args) (list 'cdr var)
            ;; (cons (list (car args) . (list (list 'car var))) result)))
            (put-assoc-eq (car args) (list 'car var) result)))
))

(defun map-arguments (arg-names args result)
    (cond ((null args) result)
        ; if argument is a variable (or a base ctor),
        ; associate it with the corresponding arg-name
        ((variablep (car args))
            (map-arguments (cdr arg-names) (cdr args)
                (put-assoc-equal (car args) (car arg-names) result)))
        ; otherwise associate it with its arg-name and
        ; associate all subterms with list elements
        (t (map-arguments (cdr arg-names) (cdr args)
            (put-assoc-equal (car args) (car arg-names)
                (car-cdr-gen (cdar args) (car arg-names) result)))))
)

(defun create-pred (len var)
    (cond ((equal len 0) (list 'endp var))
        ;; ((> len 1)
        ;;     (list (quote and) (list 'consp var)
        ;;         (list 'equal (list 'length var) len)))
        (t 't))
)

(defun create-cond (ctors arg-alist arg-types args)
    (cond ((null args) 't)
        ((listp (car args))
            (let* (
                (ctor-list (cdr (assoc-equal (car arg-types) ctors)))
                (ctor-len (cdr (assoc-equal (caar args) ctor-list)))
                (var (cdr (assoc-equal (car args) arg-alist))))
            (list 'and (create-pred ctor-len var)
                (create-cond ctors arg-alist (cdr arg-types) (cdr args)))))
        (t (create-cond ctors arg-alist (cdr arg-types) (cdr args))))
)

(defun create-case1 (ctors arg-names arg-types def)
    (let ((arg-alist (map-arguments arg-names (cdr (second def)) nil)))
        (list (create-cond ctors arg-alist arg-types (cdr (second def)))
            (mv-let (changedp val)
                (sublis-var1 arg-alist (third def))
                (declare (ignore changedp))
                val))
))

(defun create-case (ctors arg-names arg-types def)
    (cond
        ((equal (car def) 'forall)
            (create-case1 ctors arg-names arg-types (third def)))
        (t (create-case1 ctors arg-names arg-types def))
))

(defun process-ctors (ctors)
    (cond ((null ctors) nil)
        (t (cons (cons (caar ctors) (length (cdar ctors)))
            (process-ctors (cdr ctors)))))
)

(defun add-datatypes1 (names types type-alist)
    (cond ((null names) type-alist)
        (t (add-datatypes1 (cdr names) (cdr types)
            (put-assoc-equal (caar names) (process-ctors (car types)) type-alist))))
)

(defun add-datatypes (types type-alist)
    (let ((name-list (car types)) (types-list (cadr types)))
        (add-datatypes1 name-list types-list type-alist))
)

(defun add-conjecture (def)
    (cond
        ((equal (car def) 'forall)
            (add-conjecture (third def)))
        ((equal (car def) '=)
            (list (list 'defthm 'theorem (cons 'equal (cdr def))))))
)

(defun get-function-symbol (def)
    (cond
        ((equal (car def) 'forall) (get-function-symbol (caddr def)))
        (t (caadr def)))
)

(defun create-arg-names (args result)
    (cond ((null args) result)
        (t (create-arg-names (cdr args) (append result (list (genvar 'genvar "X" 0 result))))))
)

(defun process-declare-fun (def func-alist)
    (let ((name (car def)) (args (create-arg-names (cadr def) nil)))
        (put-assoc-equal name (list args (cadr def)) func-alist))
)

(defun process-assert (def type-alist func-alist func-cases-alist)
    (let* (
        (func (get-function-symbol def))
        (kv (assoc-equal func func-alist))
        (cases (assoc-equal func func-cases-alist)))
            (put-assoc-equal func (append (cdr cases)
                (list (create-case type-alist (cadr kv) (caddr kv) def))) func-cases-alist))
)

(defun process-object (obj type-alist func-alist func-cases-alist conjectures)
    (let ((fn (car obj)) (args (cdr obj)))
        (cond
            ((equal fn 'declare-fun)
                (mv type-alist
                    (process-declare-fun args func-alist)
                    func-cases-alist
                    conjectures))
            ((equal fn 'declare-datatypes)
                (mv (add-datatypes args type-alist)
                    func-alist
                    func-cases-alist
                    conjectures))
            ((equal fn 'assert)
                (cond
                    ((equal (caar args) 'not)
                        (mv type-alist
                            func-alist
                            func-cases-alist
                            (append conjectures (add-conjecture (cadar args)))))
                    (t
                        (mv type-alist
                            func-alist
                            (process-assert
                            (car args) type-alist func-alist func-cases-alist)
                            conjectures))))
            (t (mv type-alist func-alist func-cases-alist conjectures))
)))

(defun process-objects (objects type-alist func-alist func-cases-alist conjectures)
    (cond ((null objects) (mv type-alist func-alist func-cases-alist conjectures))
        (t (mv-let (type-alist func-alist func-cases-alist conjectures)
            (process-object (car objects) type-alist func-alist func-cases-alist conjectures)
            (process-objects (cdr objects) type-alist func-alist func-cases-alist conjectures))))
)

(defun create-defun (name args cases)
    (list 'defun name args (cons 'cond cases))
)

(defun create-defuns1 (func-list func-alist)
    (cond ((null func-list) nil)
        (t (let* (
            (name (caar func-list))
            (args (cadr (assoc-equal name func-alist)))
            (cases (cdar func-list)))
                (cons (create-defun name args cases)
                    (create-defuns1 (cdr func-list) func-alist)))))
)

(defun generate-ctor-args (len result)
    (cond ((zp len) result)
        (t (generate-ctor-args (1- len)
        (append result (list (genvar 'genvar "X" 0 result))))))
)

(defun create-ctor-defun (name len)
    (cond ((zp len) nil)
        (t (let ((args (generate-ctor-args len nil)))
            (list 'defun name args (cons 'list args)))))
)

(defun create-ctor-defuns1 (type-list)
    (cond ((null type-list) nil)
        (t (cons (create-ctor-defun (caar type-list) (cdar type-list))
            (create-ctor-defuns1 (cdr type-list)))))
)

(defun create-ctor-defuns (type-list)
    (cond ((null type-list) nil)
        (t (append (create-ctor-defuns1 (cdar type-list)) (create-ctor-defuns (cdr type-list)))))
)

(defun create-defuns (type-alist func-list func-alist)
    (append (create-ctor-defuns type-alist)
        (create-defuns1 func-list func-alist))
)

(defun read-file1 (current-list channel state)
    (mv-let (eofp obj state)
        (read-object channel state)
        (cond
            (eofp (mv current-list state))
            (t (read-file1 (cons obj current-list)
                    channel state))))
)

(defun read-smt-file (filename state)
    (mv-let (channel state)
        (open-input-channel filename :object state)
        (mv-let (result state)
            (read-file1 nil channel state)
            (let ((state (close-input-channel channel state)))
                (mv (reverse result) state))))
)

(defun process-file (filename state)
    (mv-let (result state) (read-smt-file filename state)
        (mv-let (type-alist func-alist func-cases-alist conjectures)
            (process-objects result nil nil nil nil)
            (mv (append (create-defuns type-alist func-cases-alist func-alist)
                    conjectures) state)))
)

:logic
:q
(save-exec "smtlib-to-acl2" nil
           :return-from-lp
           '(mv-let (argv state) (oslib::argv)
                (mv-let (defs state) (process-file (car argv) state)
                    (ld defs :ld-pre-eval-print t))))
