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
                (car-cdr-gen (cdar args) (list 'cdr (car arg-names)) result)))))
)

; creates a predicate for a list variable
; based on its length
(defun create-pred (len var name)
    (cond ((zp len) (list (list 'endp var) (list 'equal var (list 'quote name))))
        (t (list (list 'consp var) (list 'equal (list 'car var) (list 'quote name))
            ; As ACL2 expects total functions, it sometimes
            ; cannot accept functions which handles only
            ; one length apart from the base cases. This
            ; is okay to leave out if there is only one
            ; non-base ctor but if there are two or more,
            ; some heuristic will be needed to handle them
            ; separately
            ;; (list 'equal (list 'length var) len)
        )))
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
                        (create-pred ctor-len var (caar args))))
                    ; argument may be a zero length ctor
                    ((assoc-equal (car args) (cdr (assoc-equal (car arg-types) ctors)))
                        (let ((ctor-len (cdr (assoc-equal (car args) ctor-list))))
                        (create-pred ctor-len var (car args))))
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

(defun add-datatype (name types type-alist)
    (put-assoc-equal name (process-ctors types) type-alist)
)

; Converts a list of datatypes to an alist of their names
; with an associated alist of ctors and ctor lengths
(defun add-datatypes1 (names types type-alist)
    (cond ((null names) type-alist)
        (t (add-datatypes1 (cdr names) (cdr types)
            (add-datatype (caar names) (car types) type-alist))))
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

(defun parse-arg-types (args)
    (cond ((null args) nil)
        (t (cons (cadar args) (parse-arg-types (cdr args)))))
)

(defun parse-arg-names (args)
    (cond ((null args) nil)
        (t (cons (caar args) (parse-arg-names (cdr args)))))
)

(defun process-header (name args func-alist)
    (let ((arg-names (parse-arg-names args))
        (arg-types (parse-arg-types args)))
        (put-assoc-equal name (list arg-names arg-types) func-alist))
)

(mutual-recursion
(defun process-match-case (var case condition arg-alist)
    (let ((arg-alist
            (cond ((listp (car case)) (put-assoc-equal (car case) var 
                    (car-cdr-gen (car case) (list 'cdr var) arg-alist)))
                (t arg-alist)))
        (ctor-len (cond ((listp (car case)) (length (cdar case))) (t 0)))
        (ctor-name (cond ((listp (car case)) (caar case)) (t (car case)))))
        (process-block (cadr case)
            (append (create-pred ctor-len var ctor-name) condition)
            arg-alist))
)

(defun process-match (var def condition arg-alist)
    (cond ((null def) nil)
        (t (cons (process-match-case var (car def) condition arg-alist)
            (process-match var (cdr def) condition arg-alist))))
)

(defun process-block (blk condition arg-alist)
    (let ((fn (car blk)))
        (cond ((equal fn 'match) (process-match (cadr blk) (caddr blk) condition arg-alist))
            ; TODO: handle other keywords
            (t (list (conjunct-conds condition)
                (mv-let (changedp val)
                    (sublis-var1 arg-alist blk)
                    (declare (ignore changedp))
                    val)))))
)
)

(defun process-rec-fun (def defs)
    (let* (
        (name (car def))
        (args (cadr def))
        (defs (change-definitions defs :funcs
            (process-header name args (definitions->funcs defs)))))
            (change-definitions defs :func-cases
                (put-assoc-equal name (process-block (cadddr def) nil nil)
                    (definitions->func-cases defs))))
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
            ((equal fn 'declare-datatype)
                (change-definitions defs :types
                    (add-datatype (car args) (cadr args) (definitions->types defs))))
            ((equal fn 'declare-datatypes)
                (change-definitions defs :types
                    (process-datatypes args (definitions->types defs))))
            ((equal fn 'define-fun-rec)
                (process-rec-fun args defs))
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

; All failed definitions will cause the read-eval-print loop
; to exit with 1 or otherwise exit with 0 in the end
(defun add-error-handling (defs)
    (cond ((null defs) (list '(exit 0)))
        ((null (car defs)) (add-error-handling (cdr defs)))
        (t (cons (list 'mv-let '(erp val state) (car defs)
                '(declare (ignore val))
                '(prog2$ (if erp (exit 1) nil) state))
            (add-error-handling (cdr defs)))))
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
                    (ld (add-error-handling defs) :ld-pre-eval-print t))))
