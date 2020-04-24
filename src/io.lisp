(in-package "ACL2")

(set-state-ok t)

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
