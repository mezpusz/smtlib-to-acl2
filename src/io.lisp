(in-package "ACL2")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "oslib/argv" :dir :system)

(set-state-ok t)

(table acl2-defaults-table :defun-mode :program)

(std::defaggregate options
    ((debug-theorem booleanp)
    (time-limit natp)
    (debug-definitions booleanp)
    (generalize booleanp)
    (filename stringp)))

(defun split-equals (arg)
    (let* ((x (str::str-fix arg))
        (pos (str::strpos "=" x)))
            (cond (pos
                (mv (subseq x 0 pos)
                    (subseq x (+ 1 pos) nil)))
                (t (mv (subseq x 0 pos) nil))))
)

(defun parse-args1 (input opts)
    (cond ((endp input) opts)
        ((str::strprefixp "--" (car input))
        (parse-args1 (cdr input)
            (mv-let (name val)
                (split-equals (subseq (car input) 2 nil))
                (cond ((string-equal name "debug-theorem") (change-options opts :debug-theorem t))
                    ((string-equal name "debug-definitions") (change-options opts :debug-definitions t))
                    ((string-equal name "time-limit") (change-options opts :time-limit (str::strval val)))
                    ((string-equal name "generalize") (change-options opts :generalize t))
                    (t opts)))
        ))
        (t (parse-args1 (cdr input) (change-options opts :filename (car input)))))
)

(defun parse-args (state)
    (mv-let (argv state) (oslib::argv)
        (mv (parse-args1 argv (make-options :filename "" :time-limit 0)) state))
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
