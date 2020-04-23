:set-state-ok t
:program
(set-ld-error-action :return! state)

(include-book "oslib/argv" :dir :system)
(include-book "std/util/defaggregate" :dir :system)

(include-book "io" :load-compiled-file nil)

(std::defaggregate definitions
    ((types listp)
    (funcs listp)
    (func-cases listp)
    (conjectures listp)))

; associates all args with a selector
; for their position in the argument list
; in the given alist result
(defun car-cdr-gen (args var result)
    (cond ((null args) result)
        (t (car-cdr-gen (cdr args) (list 'cdr var)
            (put-assoc-eq (car args) (list 'car var) result)))
))

; maps a list of arguments to variable names;
; compound terms are mapped recursively
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

; creates a predicate for a list variable
; based on its length
(defun create-pred (len var)
    (cond ((zp len) (list (list 'endp var)))
        (t (list (list 'consp var)
            (list 'equal (list 'length var) len))))
)

; creates a conjuct for all predicates made for
; all arguments in the args based on their types
; (which now concerns only the length of ctors)
(defun create-cond (ctors arg-names arg-types args)
    (let ((ctor-list (cdr (assoc-equal (car arg-types) ctors)))
        (var (car arg-names)))
        (cond ((null args) nil)
            ((listp (car args))
                (let ((ctor-len (cdr (assoc-equal (caar args) ctor-list))))
                (append (create-pred ctor-len var)
                    (create-cond ctors (cdr arg-names) (cdr arg-types) (cdr args)))))
            ((assoc-equal (car args) (cdr (assoc-equal (car arg-types) ctors)))
                (let ((ctor-len (cdr (assoc-equal (car args) ctor-list))))
                (append (create-pred ctor-len var)
                    (create-cond ctors (cdr arg-names) (cdr arg-types) (cdr args)))))
            (t (create-cond ctors (cdr arg-names) (cdr arg-types) (cdr args)))))
)

(defun conjunct-conds (conds)
    (cond
        ((> (length conds) 1) (cons 'and conds))
        (t (car conds)))
)

(defun create-case-eq (ctors arg-names arg-types def)
    (let ((arg-alist (map-arguments arg-names (cdr (second def)) nil)))
        (list (conjunct-conds (create-cond ctors arg-names arg-types (cdr (second def))))
            (mv-let (changedp val)
                (sublis-var1 arg-alist (third def))
                (declare (ignore changedp))
                val)))
)

(defun create-case-lit (ctors arg-names arg-types def pol)
    (list (conjunct-conds (create-cond ctors arg-names arg-types (cdr def))) pol)
)

(defun create-case (ctors arg-names arg-types def pol)
    (cond
        ; throw the quantifier away and process subformula
        ((equal (car def) 'forall)
            (create-case ctors arg-names arg-types (third def) pol))
        ((equal (car def) 'not)
            (create-case ctors arg-names arg-types (second def) (not pol)))
        ((equal (car def) '=)
            ; TODO: find out how to handle polarity here
            (create-case-eq ctors arg-names arg-types def))
        (t
            (create-case-lit ctors arg-names arg-types def pol)))
)

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
            (list (list 'defthm 'theorem (cons 'equal (cdr def)))))
        (t
            (list (list 'defthm 'theorem def))))
)

(defun wrap-conjecture (conj enable)
    (cond (enable (list (list 'with-output
            ':off ':all
            ;; ':on '(prove summary)
            ':on '(summary)
            ':gag-mode 'nil (car conj))))
        (t conj))
)

(defun get-function-symbol (def)
    (cond
        ((equal (car def) 'forall) (get-function-symbol (caddr def)))
        ((equal (car def) 'not) (get-function-symbol (cadr def)))
        ((equal (car def) '=) (caadr def))
        (t (car def)))
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
                (list (create-case type-alist (cadr kv) (caddr kv) def 't))) func-cases-alist))
)

(defun process-object (obj defs)
    (let ((fn (car obj)) (args (cdr obj)))
        (cond
            ((equal fn 'declare-fun)
                (change-definitions defs :funcs
                    (process-declare-fun args (definitions->funcs defs))))
            ((equal fn 'declare-datatypes)
                (change-definitions defs :types
                    (add-datatypes args (definitions->types defs))))
            ((equal fn 'assert)
                (cond
                    ((equal (caar args) 'not)
                        (change-definitions defs :conjectures
                            (append (definitions->conjectures defs)
                                (wrap-conjecture (add-conjecture (cadar args)) t))))
                    (t
                        (change-definitions defs :func-cases
                            (process-assert
                                (car args) (definitions->types defs)
                                (definitions->funcs defs) (definitions->func-cases defs))))))
            (t defs)))
)

(defun process-objects (objs defs)
    (cond ((null objs) defs)
        (t (let ((defs (process-object (car objs) defs)))
            (process-objects (cdr objs) defs))))
)

(defun create-defun (name args cases)
    (list 'with-output
            ':off ':all
            (list 'defun name args (cons 'cond cases)))
)

(defun add-else-case (cases)
    (cond ((equal (length cases) 1) (list (list 't (cadar cases))))
        (t (cons (car cases) (add-else-case (cdr cases)))))
)

(defun create-defuns1 (func-list func-alist)
    (cond ((null func-list) nil)
        (t (let* (
            (name (caar func-list))
            (args (cadr (assoc-equal name func-alist)))
            (cases (add-else-case (cdar func-list))))
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

(defun create-defuns (defs)
    (append (create-ctor-defuns (definitions->types defs))
        (create-defuns1 (definitions->func-cases defs)
                        (definitions->funcs defs)))
)

(defun rename-defined-objects (objs)
    (sublis (list (cons 'cons 'cons_)
            (cons 't 't_)) objs)
)

(defun process-file (filename state)
    (mv-let (objs state) (read-smt-file filename state)
        (let* ((proc-objs (rename-defined-objects objs))
            (defs (process-objects proc-objs (make-definitions :types nil
                                                          :funcs nil
                                                          :func-cases nil
                                                          :conjectures nil))))
            (mv (append (create-defuns defs)
                    (definitions->conjectures defs))
                state)))
)

; Add these to the beginning of the block to be debugged
;; (let ((x (break$)))
;; (declare (ignore x))

; Uncomment this to enable debugging
;; (set-debugger-enable t)

:logic
:q
(save-exec "smtlib-to-acl2" nil
           :return-from-lp
           '(mv-let (argv state) (oslib::argv)
                (mv-let (defs state) (process-file (car argv) state)
                    (ld defs :ld-pre-eval-print t))))
