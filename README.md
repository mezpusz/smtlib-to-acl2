#SMTLIB-to-ACL2
## Project motivation
The aim of this project is to generate [ACL2](http://www.cs.utexas.edu/users/moore/acl2/) inductive proofs based on [SMTLIB](http://smtlib.cs.uiowa.edu/) problem specifications. Both formats are LISP, therefore ACL2 was found suitable for the conversion and also for running the generated scripts. The term algebra given by the SMTLIB problem is converted into a set of lists such that a constructor of length $n$ will be converted into a list of length $n$. This effectively hides the intended meaning of the term algebra so ACL2 can focus on the proofs. 

## SMTLIB format
Although the SMTLIB offers a rich set of tools to describe problems, only the `declare-datatypes`, `declare-fun` and `assert` declarations are handled. This is enough for the current use-case but needs extending in the future.

## Requirements
* Unix environment
* ACL2

## Building and running
After setting the environment variable `ACL2` to the appropriate executable for ACL2, just hit the following:
```./build.sh```
This creates a standalone binary and runner script named as `smtlib-to-acl2.core` and `smtlib-to-acl2`, respectively.
This latter script can be run already, but the user will encounter the ACL2 io-loop after the generated definitions are dealt with and needs to type `(exit)` to get back to the Terminal. For convenience, the user can run the following to exit immediately: 
```./run.sh```

## Known issues
* As ACL2 expects total functions, the functions generated need to be precisely given to handle all kinds of inputs so the theorems to-be-proven are also provable in these edge cases. The current version does not distinguish between the constructors of non-zero length to achieve this property but this means any term algebra with more than one constuctor of non-zero length won't be handled correctly.
* The SMTLIB format 
