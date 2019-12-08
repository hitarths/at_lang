# atpy
##### Array Theory Program Verification with z3py

The tool can be used to verify and localize bug in program involving arrays. The program must be written in
the *at* language. The grammar of this accepted langauge is pretty much like C. Please refer to the `atpy.py` file to see the complete grammar.

The tools runs on `Python 3.6`.

The tool performs following four steps:
* **Parser:** Reads the program and converts it to a tree for further processing. We have used Lark (Python Library) for that.
* **Encoding as Z3 constraints:** In this module, given the parsed tree of the program, we get the precondition, postcondition and program in logical form as Z3 constraints (while converting the program to SSA).
* **Verifier:** Given the precondition, postcondition and the program execution encoded as Z3 constraints, we proceed to verify the program by calling the solver on the constraints as described earlier.
* **Bug Localizer:** If the program verification fails in the 3rd module, then this module tries to find the unsat core of the constraint system, as described previously, to localize the possible statements cause of the error.


#### Note: The tool doesn't supports loops yet. Also, there could be only one `if-else` block in the program.

The examples are provided in the root directory. To verify a program, use following command from the repo directory:

`$ python atpy.py filename.atlang`

The output displays whether the given program is valid or not, and if the tool finds out possible buggy lines, it prints them.
