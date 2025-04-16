## e-star-compiler-frontend

Bringing memory into E: a front-end compiler for an imperative language built from the E language concrete syntax ([http://erights.org/elang/](http://erights.org/elang/)) with support for pointers.  
The compiler outputs an intermediate representation called *Three Address Code*.

| Tool      | Version  |
|-----------|----------|
| BNFC      | 2.9.5    |
| Alex      | 3.5.1.0  |
| Happy     | 2.0.2    |
| GHC       | 9.8.2    |

To compile the sources, run the `make` command.  
To run a demo, use the `make demo` command.  
The `tests` folder contains 14 example programs that can be executed by running `cabal repl main` and calling the function `testFile` followed by the file path.

---

## Relevant design choices

* The syntax is E-like but distinguishes between statements and expressions.
* The language is *almost* eager (except for boolean expressions, which are evaluated lazily).
* Scoping is *full* within a block (i.e., visibility is allowed above the definition point) only for functions and compile-time constants, not for variables.  
  Since the evaluation strategy is eager, mutual definitions of variables or constants are not allowed (though they are allowed for functions).
* Expressions and actual parameters are evaluated from left to right.
* Assignments evaluate the left-hand expressions first.
* A program written in this language consists of a sequence of blocks (instruction sequences) with no explicit entry point (`main()`).
* Variables and constants share the same namespace, while functions and procedures have their own separate namespace.

---

## Supported functionalities

* Declaration of variables and compile-time constants
* Declaration and invocation of functions and procedures
* Variable assignments, including syntactic sugar like `+=`, `-=`, etc.
* Increment and decrement operators: `x++`, `++x`, `y--`, `--y`
* Statically sized arrays of any type and dimension
* Array assignments
* Pointers (using `@`)
* Standard mathematical and boolean expressions
* Conditional structures and loops (`if`, `if-else`, determinate and indeterminate loops), with support for `break` and `continue` directives
* Parameter passing modes: by value, by reference, by result, and by value-result

---

The following table lists the supported operators and their usual semantics.


| Operator  | Precedence  | Associativity  |
| :----:    |    :----:   |          :----: |
| \|\|      | 1           | left            |
| &&        | 2           | left            |
|!          | 3           |                 |
|==, !=, <, <=, >, >=| 4  |                 |
|+, - (binary)| 5        | left            |
|*, /, %    | 6           | left            |
|**         | 7           | right           |
|- (unary) | 8           |                 |
|++, -- (pre e post)| 9   |                 |
|& (reference), $ (dereference)       | 10          |                 |





