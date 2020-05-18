
(in-package "ACL2")

(table acl2-defaults-table :defun-mode :program)

; Add (and ...) wrapper to conditions if there are more than one
(defun conjunct-conds (conds)
    (cond
        ((> (length conds) 1) (cons 'and conds))
        (t (car conds)))
)

; creates a predicate for a list variable
; based on its length and name
(defun create-pred-named (len var name)
    (cond ((zp len) (list (list 'endp var) (list 'equal var (list 'quote name))))
        (t (list (list 'consp var) (list 'equal (list 'car var) (list 'quote name)))))
)

(defun create-pred (len var)
    (cond ((zp len) (list (list 'endp var)))
        (t (list (list 'consp var))))
)

(defun is-similar-case (arg case other arg-names arg-types type-alist)
    (cond ((null case) t)
        (t (let ((arg1 (car case)) (arg2 (car other))
                (ctor-list (cdr (assoc-equal (car arg-types) type-alist))))
            (cond ((or (equal arg1 arg2) ; same case
                    ; or selected argument position in this and in other case
                    ; are both base cases or recursive cases
                    (and (equal arg (car arg-names))
                        (assoc-equal arg1 ctor-list) (assoc-equal arg2 ctor-list)
                        (equal (zp (cdr (assoc-equal arg1 ctor-list)))
                            (zp (cdr (assoc-equal arg2 ctor-list))))))
                    (is-similar-case arg (cdr case) (cdr other) (cdr arg-names)
                        (cdr arg-types) type-alist))
                    (t nil)))))
)

(defun is-last-case (arg case next-cases arg-names arg-types type-alist)
    (cond ((null next-cases) t)
        (t (and (not (is-similar-case arg (car case) (caar next-cases) arg-names arg-types type-alist))
            (is-last-case arg case (cdr next-cases) arg-names arg-types type-alist))))
)

(defun create-function-case-cond (arg-names conds case next-cases arg-names-orig arg-types type-alist)
    (cond ((null conds) nil)
        ((null (car conds)) (create-function-case-cond (cdr arg-names) (cdr conds)
            case next-cases arg-names-orig arg-types type-alist))
        (t (let* ((ctor-list (cdr (assoc-equal (car arg-types) type-alist)))
            (ctor-len (cdr (assoc-equal (car conds) ctor-list))))
            (append (cond ((is-last-case (car arg-names) case
                                next-cases arg-names-orig arg-types type-alist)
                            (create-pred ctor-len (car arg-names)))
                        (t (create-pred-named ctor-len (car arg-names) (car conds))))
                (create-function-case-cond (cdr arg-names) (cdr conds)
                    case next-cases arg-names-orig arg-types type-alist)))))
)

(defun postprocess-function-case (case next-cases arg-names arg-types type-alist)
    (cons (conjunct-conds
        (create-function-case-cond arg-names (car case) case next-cases arg-names arg-types type-alist))
        (cdr case))
)

(defun postprocess-function-cases2 (arg-names arg-types cases type-alist)
    (cond ((null cases) nil)
        (t (cons (postprocess-function-case
            (car cases) (cdr cases) arg-names arg-types type-alist)
            (postprocess-function-cases2 arg-names arg-types (cdr cases) type-alist))))
)

(defun postprocess-function-cases1 (funcs func-cases type-alist)
    (cond ((null funcs) nil)
        (t (let* ((current (car funcs))
            (name (car current))
            (arg-names (cadr current))
            (arg-types (caddr current))
            (cases (cdr (assoc-equal name func-cases))))
            (put-assoc-equal name (postprocess-function-cases2 arg-names arg-types cases type-alist)
                (postprocess-function-cases1 (cdr funcs) func-cases type-alist)))))
)

(defun postprocess-function-cases (defs)
    (let ((funcs (definitions->funcs defs))
        (func-cases (definitions->func-cases defs))
        (types (definitions->types defs)))
        (change-definitions defs :func-cases
            (reverse (postprocess-function-cases1 funcs func-cases types))))
)
