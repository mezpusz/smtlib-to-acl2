(in-package "ACL2")

(include-book "definitions" :load-compiled-file nil)

(table acl2-defaults-table :defun-mode :program)

(defconst *redefine-list*
    (list (cons 'cons 'cons_)
          (cons 't 't_)
          (cons 'true 't)
          (cons '=> 'implies)
        ;;   (cons 'nil 'nil_)
          (cons 'equal 'equal_)
          (cons 'false '(not t)))
)

(defun add-conjecture (def opts)
    (cond
        ((equal (car def) 'forall)
            (add-conjecture (third def) opts))
        ((options->generalize opts)
            (list (list 'defthm 'theorem def
                ':hints '(("Goal" :generalize t)))))
        (t
            (list (list 'defthm 'theorem def ':rule-classes 'nil))))
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

(defun wrap-conjecture (def opts)
    (time-limit-conjecture
        (debug-conjecture
            (add-conjecture def opts) opts) opts)
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

; There are a couple of names that may clash with
; the ACL2 definitions, we simply rename these
(defun rename-defined-objects (objs)
    (sublis *redefine-list* objs)
)
