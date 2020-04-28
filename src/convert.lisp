:set-state-ok t
:program
(set-ld-error-action :return! state)

(include-book "oslib/argv" :dir :system)

(include-book "src/definitions" :load-compiled-file nil)
(include-book "src/io" :load-compiled-file nil)
(include-book "src/acl2" :load-compiled-file nil)

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
    ; get ctors for current argument type
    (let ((ctor-list (cdr (assoc-equal (car arg-types) ctors)))
        (var (car arg-names)))
        (cond ((null args) nil)
            (t (append
                (cond
                    ; argument is a compound expression
                    ((listp (car args))
                        (let ((ctor-len (cdr (assoc-equal (caar args) ctor-list))))
                        (create-pred ctor-len var)))
                    ; argument may be a zero length ctor
                    ((assoc-equal (car args) (cdr (assoc-equal (car arg-types) ctors)))
                        (let ((ctor-len (cdr (assoc-equal (car args) ctor-list))))
                        (create-pred ctor-len var)))
                    ; otherwise it is a variable and it doesn't need any condition
                    (t nil))
                (create-cond ctors (cdr arg-names) (cdr arg-types) (cdr args))))))
)

; Add (and ...) wrapper to conditions if there are more than one
(defun conjunct-conds (conds)
    (cond
        ((> (length conds) 1) (cons 'and conds))
        (t (car conds)))
)

; Creates a (condition term) pair from an equality
(defun create-case-eq (ctors arg-names arg-types def)
    ; map arguments of the left hand side to function variables or list expressions
    (let ((arg-alist (map-arguments arg-names (cdr (second def)) nil)))
        (list (conjunct-conds (create-cond ctors arg-names arg-types (cdr (second def))))
            ; change arguments to mapped values in right hand side
            ; TODO: find out why this doesn't work with sublis
            (mv-let (changedp val)
                (sublis-var1 arg-alist (third def))
                (declare (ignore changedp))
                val)))
)

; Creates a (condition term) pair from a non-equality (predicate formula)
(defun create-case-formula (ctors arg-names arg-types def pol)
    ; Here the trick is we create the condition from the formula itself
    ; and return the current polarity (this may not work in some cases)
    (list (conjunct-conds (create-cond ctors arg-names arg-types (cdr def))) pol)
)

; Creates a function case
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
            (create-case-formula ctors arg-names arg-types def pol)))
)

; Converts a list of ctors, e.g. ((zero) (s (s0 nat)))
; to a list of ctor names and their sizes, e.g. ((zero . 0) (s . 1))
(defun process-ctors (ctors)
    (cond ((null ctors) nil)
        (t (cons (cons (caar ctors) (length (cdar ctors)))
            (process-ctors (cdr ctors)))))
)

; Converts a list of datatypes to an alist of their names
; with an associated alist of ctors and ctor lengths
(defun add-datatypes1 (names types type-alist)
    (cond ((null names) type-alist)
        (t (add-datatypes1 (cdr names) (cdr types)
            (put-assoc-equal (caar names) (process-ctors (car types)) type-alist))))
)

; Wrapper function for processing datatypes
(defun process-datatypes (types type-alist)
    (let ((name-list (car types)) (types-list (cadr types)))
        (add-datatypes1 name-list types-list type-alist))
)

; Gets the current function symbol which is the first
; non-logical left-hand side list's first symbol
(defun get-function-symbol (def)
    (cond
        ((equal (car def) 'forall) (get-function-symbol (caddr def)))
        ((equal (car def) 'not) (get-function-symbol (cadr def)))
        ((equal (car def) '=) (caadr def))
        (t (car def)))
)

; Generates a list of new argument variables
; using the list in-the-making as an avoid list
(defun create-arg-names (args result)
    (cond ((null args) result)
        (t (create-arg-names (cdr args)
            (append result (list (genvar 'genvar "X" 0 result))))))
)

; Adds a (name arg-names arg-types) entry to the function alist
(defun process-declare-fun (def func-alist)
    (let ((name (car def)) (args (create-arg-names (cadr def) nil)))
        (put-assoc-equal name (list args (cadr def)) func-alist))
)

; After an assert is believed to be a recursive case of a function
; it gets processed from the outside with positive polarity and gets
; added to the case alist of the respective function
(defun process-assert (def type-alist func-alist func-cases-alist)
    (let* (
        (func (get-function-symbol def))
        (kv (assoc-equal func func-alist))
        (cases (assoc-equal func func-cases-alist)))
            (put-assoc-equal func (append (cdr cases)
                (list (create-case type-alist (cadr kv) (caddr kv) def 't))) func-cases-alist))
)

; Process one SMTLIB definition
; Only declare-fun, declare-datatypes and assert
; definitions are processed otherwise they are thrown away
(defun process-object (obj defs opts)
    (let ((fn (car obj)) (args (cdr obj)))
        (cond
            ((equal fn 'declare-fun)
                (change-definitions defs :funcs
                    (process-declare-fun args (definitions->funcs defs))))
            ((equal fn 'declare-datatypes)
                (change-definitions defs :types
                    (process-datatypes args (definitions->types defs))))
            ((equal fn 'assert)
                (cond
                    ; The conjecture starts with a 'not' in a refutation
                    ; format, although it can also be a quantifier-free
                    ; function definition formula starting with 'not'
                    ; TODO: create a better way of spotting the conjecture
                    ((equal (caar args) 'not)
                        (change-definitions defs :conjectures
                            (append (definitions->conjectures defs)
                                (wrap-conjecture (cadar args) opts))))
                    (t
                        (change-definitions defs :func-cases
                            (process-assert
                                (car args) (definitions->types defs)
                                (definitions->funcs defs) (definitions->func-cases defs))))))
            (t defs)))
)

(defun process-objects (objs defs opts)
    (cond ((null objs) defs)
        (t (let ((defs (process-object (car objs) defs opts)))
            (process-objects (cdr objs) defs opts))))
)

(defun process-file (opts state)
    (mv-let (objs state) (read-smt-file (options->filename opts) state)
        (let* ((proc-objs (rename-defined-objects objs))
            (defs (process-objects proc-objs (make-definitions) opts)))
            (mv (append (create-defuns defs opts)
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
           '(mv-let (opts state) (parse-args state)
                (mv-let (defs state) (process-file opts state)
                    (ld defs :ld-pre-eval-print t))))
