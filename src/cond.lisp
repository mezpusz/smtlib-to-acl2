
(in-package "ACL2")

(table acl2-defaults-table :defun-mode :program)

; This file helps to organize the different cases
; a function can have: e.g. given the recursive function plus
; (define-fun-rec
;   plus
;   ((x Bin) (y Bin)) Bin
;   (match x
;     ((One (s y))
;      ((ZeroAnd z)
;       (match y
;         ((One (s x))
;          ((ZeroAnd ys) (ZeroAnd (plus z ys)))
;          ((OneAnd xs) (OneAnd (plus z xs))))))
;      ((OneAnd x2)
;       (match y
;         ((One (s x))
;          ((ZeroAnd zs) (OneAnd (plus x2 zs)))
;          ((OneAnd ys2) (ZeroAnd (s (plus x2 ys2))))))))))
; the match macros cover the following cases, which
; then should be translated into the form in the last column:
;     x       y       translated
; 1   One     _       (and (endp x) (equal x 'One))
; 2   ZeroAnd One     (and (consp x) (equal (car x) 'ZeroAnd) (endp y) (equal y 'One))
; 3   ZeroAnd ZeroAnd (and (consp x) (equal (car x) 'ZeroAnd) (consp y) (equal (car y) 'ZeroAnd))
; 4   ZeroAnd OneAnd  (and (consp x) (equal (car x) 'ZeroAnd) (consp y) (equal (car y) 'OneAnd))
; 5   OneAnd  One     (and (consp x) (equal (car x) 'OneAnd) (endp y) (equal y 'One))
; 6   OneAnd  ZeroAnd (and (consp x) (equal (car x) 'OneAnd) (consp y) (equal (car y) 'ZeroAnd))
; 7   OneAnd  OneAnd  (and (consp x) (equal (car x) 'OneAnd) (consp y) (equal (car y) 'OneAnd))
;
; However, because ACL2 except total function, all cases that are not covered (e.g.
; (and (endp x) (not (equal x 'One)))) will be assumed to be nil (= false), therefore
; ACL2 can infer things such as (implies (endp x) (equal x 'One)) which it then throws
; away as a non-theorem and fails.
; To mitigate this issue, an individual condition c on an argument x in a function case
; is reduced if:
; * this function case is of the form (c1 c2 ... ci-1 ci ci+1 ... cn)
;   where c1 to cn are conditions and x is the argument for position i (ci = c)
; * there are no other cases that come after this function case
;   and is of the form (c1 c2 ... ci-1 di ci+1 ... cn) (i.e. they are the same except
;   ci and di) where ci and di are both recursive or both base cases
;
; In the example given, the translated forms are reduced to these:
; 1 (endp x)
; 2 (and (consp x) (equal (car x) 'ZeroAnd) (endp y))
; 3 (and (consp x) (equal (car x) 'ZeroAnd) (consp y) (equal (car y) 'ZeroAnd))
; 4 (and (consp x) (equal (car x) 'ZeroAnd) (consp y))
; 5 (and (consp x) (endp y))
; 6 (and (consp x) (consp y) (equal (car y) 'ZeroAnd))
; 7 (and (consp x) (consp y))

; Add (and ...) wrapper to conditions if there are more than one
(defun conjunct-conds (conds)
    (cond
        ((> (length conds) 1) (cons 'and conds))
        (t (car conds)))
)

; Creates a predicate for a variable
; based on its length and name
;
; This variant is used when there are still
; other cases of this type (base or recursive)
; defined later in the function and need to be
; distinguished from this one
(defun create-pred-named (len var name)
    (cond ((zp len) (list (list 'endp var) (list 'equal var (list 'quote name))))
        (t (list (list 'consp var) (list 'equal (list 'car var) (list 'quote name)))))
)

; Creates a predicate for a variable
; based on its length
;
; This variant is used when there are no more
; other cases of this type (base or recursive)
; defined later in the function so it must be
; reduced to either endp or consp to respect
; the function totalness of ACL2
(defun create-pred (len var)
    (cond ((zp len) (list (list 'endp var)))
        (t (list (list 'consp var))))
)

; This function returns true if:
; * case and other have the same cases except for arg and
; * both case and other have the same type of case at the position
;   of arg (i.e. they are both base or recursive cases)
(defun is-similar-case (arg case other arg-names arg-types type-alist)
    (cond ((null case) t)
        (t (let ((arg1 (car case)) (arg2 (car other))
                (ctor-list (cdr (assoc-equal (car arg-types) type-alist))))
            (cond ((or (equal arg1 arg2) ; same case
                    ; or selected argument position in this and in other case
                    ; are both base or recursive cases
                    (and (equal arg (car arg-names))
                        (assoc-equal arg1 ctor-list) (assoc-equal arg2 ctor-list)
                        (equal (zp (cdr (assoc-equal arg1 ctor-list)))
                            (zp (cdr (assoc-equal arg2 ctor-list))))))
                    (is-similar-case arg (cdr case) (cdr other) (cdr arg-names)
                        (cdr arg-types) type-alist))
                    (t nil)))))
)

; This function determines whether case is similar
; to any of next-cases (see is-similar-case) - if so,
; it is the last case of it's kind and its condition
; must be reduced from a named condition to an unnamed one
; to respect function totalness of ACL2
(defun is-last-case (arg case next-cases arg-names arg-types type-alist)
    (cond ((null next-cases) t)
        (t (and (not (is-similar-case arg (car case) (caar next-cases) arg-names arg-types type-alist))
            (is-last-case arg case (cdr next-cases) arg-names arg-types type-alist))))
)

; Creates the list of conditions based on each argument case in the current function case
(defun create-function-case-cond (arg-names conds case next-cases arg-names-orig arg-types type-alist)
    (cond ((null conds) nil)
        ; if current argument case is nil, no corresponding
        ; condition was given and it can be skipped
        ((null (car conds)) (create-function-case-cond (cdr arg-names) (cdr conds)
            case next-cases arg-names-orig arg-types type-alist))
        (t (let* ((ctor-list (cdr (assoc-equal (car arg-types) type-alist)))
            (ctor-len (cdr (assoc-equal (car conds) ctor-list))))
            (append
                ; check whether this is the last case for the current
                ; argument - if so, use the unnamed predicate creator
                (cond ((is-last-case (car arg-names) case
                                next-cases arg-names-orig arg-types type-alist)
                            (create-pred ctor-len (car arg-names)))
                        (t
                            (create-pred-named ctor-len (car arg-names) (car conds))))
                (create-function-case-cond (cdr arg-names) (cdr conds)
                    case next-cases arg-names-orig arg-types type-alist)))))
)

; Create a conjunction from the list of conditions given
; for this case and conses it with the case body
(defun postprocess-function-case (case next-cases arg-names arg-types type-alist)
    (cons (conjunct-conds
        (create-function-case-cond arg-names (car case) case next-cases arg-names arg-types type-alist))
        (cdr case))
)

; Goes through the list of (conds body) pairs of function cases
; and creates a (conj body) pair where conj is the conjunction
; of the translated conditions
(defun postprocess-function-cases2 (arg-names arg-types cases type-alist)
    (cond ((null cases) nil)
        (t (cons (postprocess-function-case
            (car cases) (cdr cases) arg-names arg-types type-alist)
            (postprocess-function-cases2 arg-names arg-types (cdr cases) type-alist))))
)

; Goes through all functions and translates their conditions
; into proper predicates
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

; Wrapper function to unroll the definitions and
; call the recursive functions
(defun postprocess-function-cases (defs)
    (let ((funcs (definitions->funcs defs))
        (func-cases (definitions->func-cases defs))
        (types (definitions->types defs)))
        (change-definitions defs :func-cases
            (reverse (postprocess-function-cases1 funcs func-cases types))))
)
