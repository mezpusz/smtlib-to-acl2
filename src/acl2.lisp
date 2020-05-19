(in-package "ACL2")

(include-book "definitions" :load-compiled-file nil)

(table acl2-defaults-table :defun-mode :program)

(defconst *redefine-list*
    (list (cons 'cons 'cons_)
          (cons 't 't_)
          (cons 'true 't)
          (cons '=> 'implies)
          (cons '++ '++_)
          (cons 'nil 'nil_)
          (cons 'equal 'equal_)
          (cons 'false '(not t)))
)

(mutual-recursion
(defun remove-underscored (term)
    (cond ((variablep term) term)
        ((fquotep term) term)
        ((equal (car term) '_) (remove-underscored (cadr term)))
        (t (cons (car term)
            (remove-underscored-lst (cdr term)))))
)

(defun remove-underscored-lst (lst)
    (cond ((null lst) nil)
        (t (cons (remove-underscored (car lst))
            (remove-underscored-lst (cdr lst)))))
)
)

(defun add-conjecture (def alist opts)
    (cond
        ((or (equal (car def) 'forall) (equal (car def) 'par))
            (add-conjecture (third def) alist opts))
        (t (let ((def (remove-underscored (sublis-var alist def))))
            (cond
                ((options->generalize opts)
                    (list (list 'defthm 'theorem def
                        ':hints '(("Goal" :generalize t)))))
                (t
                    (list (list 'defthm 'theorem def ':rule-classes 'nil)))))))
)

(defun debug-conjecture (conj opts)
    (list (list 'with-output
        ':off ':all
        ':on (cond ((options->debug-theorem opts) '(error prove summary))
                (t '(error summary)))
        ':gag-mode 'nil (car conj)))
)

(defun time-limit-conjecture (conj opts)
    (cond
        ((posp (options->time-limit opts))
            (list (list 'with-prover-time-limit (options->time-limit opts)
                (car conj))))
        (t conj))
)

(defun wrap-conjecture (def alist opts)
    (time-limit-conjecture
        (debug-conjecture
            (add-conjecture def alist opts) opts) opts)
)

(defun create-defun (name args cases opts)
    (list 'with-output
        ':off ':all
        ':on (cond ((options->debug-definitions opts) '(error prove summary))
            (t '(error summary)))
        (list 'defun name args (cond
            ((equal 1 (length cases)) (cadar cases))
            (t (cons 'cond cases)))))
)

(defun create-defuns1 (func-list func-alist opts)
    (cond ((null func-list) nil)
        (t (let* (
            (name (caar func-list))
            (args (cadr (assoc-equal name func-alist)))
            (cases (cdar func-list)))
            ; As ACL2 expects total functions, in some cases
            ; the generated functions get better accepted
            ; if they contain an else branch but more
            ; experimenting is needed here
            ;; (cases (add-else-case (cdar func-list))))
                (cons (create-defun name args cases opts)
                    (create-defuns1 (cdr func-list) func-alist opts)))))
)

(defun generate-ctor-args (len result)
    (cond ((zp len) result)
        (t (generate-ctor-args (1- len)
        (append result (list (genvar 'genvar "X" 0 result))))))
)

(defun create-ctor-defun (name len)
    (cond ((zp len) nil)
        (t (let ((args (generate-ctor-args len nil)))
            (list 'defun name args (cons 'list (cons (list 'quote name) args))))))
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

(defun create-defuns (defs opts)
    (append (create-ctor-defuns (definitions->types defs))
        (create-defuns1 (definitions->func-cases defs)
                        (definitions->funcs defs) opts))
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

(mutual-recursion
(defun sublis-nil (alist term)
    (let ((temp (assoc-equal term alist)))
        (cond (temp (cdr temp))
            ((variablep term) term)
            ((fquotep term) term)
            (t (cons-term (sublis-nil alist (car term))
                (sublis-nil-lst alist (cdr term))))))
)

(defun sublis-nil-lst (alist lst)
    (cond ((null lst) nil)
        (t (cons (sublis-nil alist (car lst))
            (sublis-nil-lst alist (cdr lst)))))
)
)

; There are a couple of names that may clash with
; the ACL2 definitions, we simply rename these
(defun rename-defined-objects (objs)
    (sublis-nil-lst *redefine-list* objs)
)
