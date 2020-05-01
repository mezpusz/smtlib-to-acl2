# SMTLIB-to-ACL2
## Project motivation
The aim of this project is to generate [ACL2](http://www.cs.utexas.edu/users/moore/acl2/) inductive proofs based on [SMTLIB](http://smtlib.cs.uiowa.edu/) problem specifications (given in a refutation-based manner). Both formats are LISP, therefore ACL2 was found suitable for the conversion and also for running the generated scripts. The term algebra given by the SMTLIB problem is converted into a set of lists such that a constructor of length `n` will be converted into a list of length `n`. This effectively hides the intended meaning of the term algebra so ACL2 can focus on the proofs. 

## SMTLIB format
Although the SMTLIB offers a rich set of tools to describe problems, only the `declare-datatypes`, `declare-fun` and `assert` declarations are handled. This is enough for the current use-case but needs extending in the future.

## Requirements
* Unix environment
* ACL2

## Building and running
After setting the environment variable `ACL2` to the appropriate executable for ACL2, just hit the following:
````bash
$ ./build.sh
````
This creates a standalone binary and runner script named as `smtlib-to-acl2.core` and `smtlib-to-acl2`, respectively. The user can then run the following to convert one file and give the generated definitions to ACL2:
````bash
$ ./smtlib-to-acl2 <filename>
````

## Parameters
* `<filename>`: The input file location
* `--time-limit=<seconds>`: The time limit to prove any conjecture given in a non-negative integer number of seconds
* `--debug-theorem`: Show additional information about the proof of conjectures
* `--debug-definitions`: Show additional information about the proof of the function definitions

## Known issues
* As ACL2 expects total functions, the functions generated need to be precisely given to handle all kinds of inputs so the theorems to-be-proven are also provable in these edge cases. The current version does not distinguish between the constructors of non-zero length to achieve this property but this means any term algebra with more than one constuctor of non-zero length won't be handled correctly.
* The recursive function definitions in the SMTLIB files are currently read from the `assert` blocks. They mostly contain an outermost quantifier at the least but if not, they most probably won't start with a `not` operator. The actual theorems-to-be-proven are added based only on these assumptions as any `assert` directly starting with a `not` is added as a conjecture rather than a function definition.
* There is no error handling on the level of conversion and it is only expected to work when the original format is accepted by a stuitable prover with better error handling. 
