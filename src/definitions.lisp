(in-package "ACL2")

(include-book "std/util/defaggregate" :dir :system)

(std::defaggregate definitions
    ((types listp)
    (funcs listp)
    (func-cases listp)
    (conjectures listp)))
