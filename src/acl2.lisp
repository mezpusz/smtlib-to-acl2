(in-package "ACL2")

(include-book "definitions" :load-compiled-file nil)

(table acl2-defaults-table :defun-mode :program)

(defconst *redefine-list*
    (list (cons 'cons 'cons_)
          (cons 't 't_)
          (cons 'equal 'equal_)
          (cons 'false '(not t)))
)

(defun add-conjecture (def)
    (cond
        ((equal (car def) 'forall)
            (add-conjecture (third def)))
        (t
            (list (list 'defthm 'theorem def
                ;':hints '(("Goal" :generalize t))
            ))))
)

(defun wrap-conjecture (conj enable)
    (cond (enable (list (list 'with-prover-time-limit 5
            (list 'with-output
                ':off ':all
                ;; ':on '(prove summary)
                ':on '(summary)
                ':gag-mode 'nil (car conj)))))
        (t conj))
)

(defun create-defun (name args cases)
    (list 'with-output
            ':off ':all
            ':on '(summary)
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

; There are a couple of names that may clash with
; the ACL2 definitions, we simply rename these
(defun rename-defined-objects (objs)
    (sublis *redefine-list* objs)
)
