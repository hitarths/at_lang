import lark
import z3
import sys

z3_vars = dict()
all_z3_vars = dict()
z3_assertions = list()
if_conds = list()
tree = None

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
start: precond declaration_list  stmt_list postcond
precond: "@pre(" assertion ");"             //pre condition
declaration_list: declaration+
declaration: "int" var ";"     -> integer_declaration             //declaration of integer
        | "int[]" array ";"    -> array_declaration        //declaration of array without size

stmt_list: stmt*
stmt: equalitystmt                 -> assignment         //statement
    | "if (" assertion ")" "then do {" ifblock "}" elseblock?  -> if

ifblock: equalitystmt* 

elseblock: "else {" equalitystmt* "}" -> else
                                            //add while and for loop here    

postcond: "@post(" assertion ");"           //post condition
assertion: expr "=" expr                    -> equality
        | expr "<" expr                     -> smaller
        | expr ">" expr                     -> greater
        | expr "<=" expr                     -> smallerequal
        | expr ">=" expr                     -> greaterequal
        | expr "=>" expr                    -> implies
        | "( Forall (" vars ") " assertion ")" -> forall
        | z3_assertion                       
        | "(" assertion "and" assertion ")" -> and
        | "(" assertion "or" assertion ")"  -> or
        | "(" "not" assertion ")"           -> not

vars: var
    | vars "," vars

z3_assertion: "{:" /[^ ]+/ ":}"

equalitystmt : var "=" expr ";"  -> equality
            |  select "=" expr ";" -> equality


equality: var "=" expr 
        | select "=" expr

expr:  "(" expr "+" expr ")"        -> add
    |  "(" expr "-" expr ")"        -> sub
    |  select                       
    |  var                          
    |  num                          

var: WORD
num: NUMBER
array: WORD
select: array "[" var "]"
    |   array "[" num "]" 

COMMENT: /#.*/
%import common.NUMBER
%import common.WORD
%import common.WS
%import common.CNAME
%ignore WS
%ignore COMMENT
""".strip()


def model_values(model):
    """Get the values out of a Z3 model.
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }

def program_to_ssa(src):   
    global z3_vars, all_z3_vars, tree, postcond_z3, precond_z3, src_lines
    src_lines = src.split("\n")
    parser = lark.Lark(GRAMMAR, propagate_positions=True)
    tree = parser.parse(src)

    preconds = tree.children[0]
    declarations = tree.children[1]
    stmts = tree.children[2]
    postcond = tree.children[3].children[0]
    global array_vars, integer_vars, if_conds
    array_vars, integer_vars = get_vars(declarations)

    all_vars = array_vars + integer_vars
    for i in set(all_vars):
        if all_vars.count(i) != 1:
            print("The variable '{}' is declared more than once!".format(i))
            return
    if check_valid_variables(tree, src):
        print("Program is syntactically correct!\n{}".format("".rjust(35, "-")))
    else: 
        return "Exiting..."

    z3_vars= {var:(z3.Int("{}_0".format(var)),0) for var in integer_vars}
    z3_vars.update({
        arr:(z3.Array("{}_0".format(arr), z3.IntSort(), z3.IntSort()),0) for arr in array_vars
        })

    for name in z3_vars:
        all_z3_vars[name+"_0"] = z3_vars[name][0]

    precond_z3 = get_z3_assertion(preconds.children[0], z3_vars)
    ## we got the procond
    # print("\nPrecondition:", precond_z3)

    ## Now we shall convert the program to SSA using following points:
    ## 1. We have to maintain a dictionary which tells us the latest numbering of a variable
    ## 2. For left side of any assignment we will use the current variable name, and on the right side we have to use
    ##    the new variable name which will be indexed by successor of the current index.
    ## 3. Only those variables will be updated in dictionary which are on right side. 
    ## 4. For the right side of an assignment we will use the updated dictionary variables.
    z3_stmt = []

    for i in range(len(stmts.children)):
        stmt_node = stmts.children[i]
        if (stmt_node.data == "assignment"):
            z3_stmt.extend(get_z3_equality_list(stmt_node, z3_vars))

        elif (stmt_node.data == "if"):             # assuming a single if block
            z3_vars_copy_1 = mycopy(z3_vars)
            z3_vars_copy_2 = dict()
            if_cond = stmt_node.children[0]
            z3_if_cond = get_z3_assertion(if_cond, z3_vars)
            if_conds.append(z3_if_cond)
            if_block = stmt_node.children[1].children
            try:
                else_block = stmt_node.children[2].children
            except:
                else_block = []

            for st in if_block:
                z3_stmt.extend(get_z3_equality_list(st, z3_vars_copy_1, True))
            for j in range(i+1, len(stmts.children)):
                st = stmts.children[j]
                z3_stmt.extend(get_z3_equality_list(st, z3_vars_copy_1))
            # change the number associated with each var in z3_vars_copy

            for k in z3_vars:
                val, index_old = z3_vars[k]
                val_new, index_new = z3_vars_copy_1[k]
                z3_vars_copy_2[k] = (val, index_new)

            for st in else_block:
                z3_stmt.extend(get_z3_equality_list(st, z3_vars_copy_2, True))
            for j in range(i+1, len(stmts.children)):
                st = stmts.children[j]
                z3_stmt.extend(get_z3_equality_list(st, z3_vars_copy_2))
            break
        else:
            pass
            # think about implementing for loop, and then maybe do that too!

    if len(if_conds) == 1: # if there is an if condition in the code
        cond = if_conds[0]
        # there was an if block
        post_cond1 = get_z3_assertion(postcond,  z3_vars_copy_1)
        post_cond2 = get_z3_assertion(postcond,  z3_vars_copy_2)
        postcond_z3 = z3.And(z3.Implies(cond, post_cond1), z3.Implies(z3.Not(cond), post_cond2))

    else:
        #there is no if block
        postcond_z3 = get_z3_assertion(postcond, z3_vars)

    ## print("\n\nPost condition:", postcond_z3)
    z3_assertions.extend(z3_stmt) # add all these assertions to the z3_assertions
    #check all the variables are correct.

def solve(src):
    global s, model, sol
    program_to_ssa(src)
    s = z3.Solver()
    for i in range(len(z3_assertions)):
        assertion = z3_assertions[i][0]
        s.assert_and_track(assertion, "p" + str(i))
    s.assert_and_track(precond_z3, "precond")
    s.assert_and_track(z3.Not(postcond_z3), "postcond")
    res = s.check()
    if (res == z3.unsat):
        print("The program is valid!")
    else:
        print("The program is invalid!\nFollowing SAT model is found:")
        model = model_values(s.model())
        for var in model:
            print("{0:15} - {1:15}".format(var, str(model[var])))
        # let us find the unsat core
        sol = z3.Solver()
        for i in range(len(z3_assertions)):
            assertion = z3_assertions[i][0]
            sol.assert_and_track(assertion, "p" + str(i))
        sol.assert_and_track(precond_z3, "precond")
        sol.assert_and_track(postcond_z3, "postcond")

        #lets add the assertion from the model
        for var in model:
            # get the actual z3 variable
            if var in all_z3_vars:
                var_z3 = all_z3_vars[var]
                sol.add(var_z3 == model[var])

        # sol must be unsatsol
        if not sol.check()== z3.unsat: 
            print("Some error has occurred!")
            return

        core = sol.unsat_core()
        print("\nFollowing are possible reason for the error:")
        count = 0
        for st_name in core:
            if str(st_name) == "precond" or str(st_name)== "postcond":
                continue
            count  += 1
            assertion_number = int(str(st_name)[1:])
            error_line = z3_assertions[assertion_number][1].line
            print("\tLine #{}: {:>10}".format(error_line, src_lines[error_line-1].strip()))

        if count ==0:
            print("\tSorry, we couldn't localize the bug!!")

def mycopy(z3_vars):
    d = dict()
    for k in z3_vars:
        var, index = z3_vars[k]
        d[k] = (var,index)
    return d


def get_z3_equality_list(stmt_node, z3_vars, direct_equality= False):
    global all_z3_vars
    z3_asserts = []
    if not direct_equality:
        stmt_node = stmt_node.children[0]  ## get the equalitystmt first

    left = stmt_node.children[0]
    right = stmt_node.children[1]
    zright = get_z3_expr(right, z3_vars)

    name = "stmt_rhs_{}".format(stmt_node.line)
    i = 0
    temp_name = name
    while (temp_name in all_z3_vars):
        temp_name = name + "_" + str(i)
        i += 1
    name = temp_name
    zright_temp = z3.Int(name)  
    z3_asserts.append(zright_temp == zright)
    all_z3_vars[name] = zright_temp

    if left.data == "select":
        # we need to update the z3_vars
        array_name = left.children[0].children[0].value
        current_label = z3_vars[array_name][1]
        current_array = z3_vars[array_name][0]
        new_label = current_label + 1
        new_name = "{}_{}".format(array_name, new_label)
        new_array = z3.Array(new_name, z3.IntSort(), z3.IntSort())
        all_z3_vars[new_name] = new_array
        if (left.children[1].data == "var"):
            index = z3_vars[left.children[1].children[0].value][0]
        else: #left children is num
            index = left.children[1].children[0].value

        store = z3.Store(current_array, index, zright_temp)
        z3_vars[array_name] = (new_array, new_label)
        z3_asserts.append(new_array == store)  #LHS equal to new variable

    if left.data == "var":
        var_name = left.children[0].value
        var_label = z3_vars[var_name][1]
        new_name = "{}_{}".format(var_name, var_label+1)
        new_var = z3.Int(new_name)
        all_z3_vars[new_name] = new_var # add the new variable to global list
        z3_vars[var_name] = (new_var, var_label + 1)
        z3_asserts.append(new_var == zright_temp)
    
    return [(assertion, stmt_node) for assertion in z3_asserts]


def get_z3_assertion(node, z3_vars):
    def get_z3_cond_in(child):
        return get_z3_assertion(child, z3_vars)

    if node.data == "assertion":
        return get_z3_cond_in(node.children[0])
    if node.data == 'and':
        return z3.And(get_z3_cond_in(node.children[0]), get_z3_cond_in(node.children[1]))
    if node.data == "or":
        return z3.Or(get_z3_cond_in(node.children[0]), get_z3_cond_in(node.children[1]))
    if node.data == "not":
        return z3.Not(get_z3_cond_in(node.children[0]))


    left = node.children[0]
    right = node.children[1]
    zleft, zright = get_z3_expr(left, z3_vars), get_z3_expr(right, z3_vars)
    if node.data == "equality":
        return (zleft == zright)
    if node.data == "smaller":
        return (zleft < zright)
    if node.data == "greater":
        return (zleft > zright)
    if node.data == "greaterequal":
        return (zleft >= zright)
    if node.data == "smallerequal":
        return (zleft <= zright)

def get_z3_expr(expr, z3_vars):
    if (expr.data == "expr"):
        return get_z3_expr(expr.children[0], z3_vars)
    if (expr.data == "add"):
        left,right = expr.children[0], expr.children[1]
        return get_z3_expr(left, z3_vars) + get_z3_expr(right,z3_vars)
    if (expr.data == "sub"):
        left,right = expr.children[0], expr.children[1]
        return get_z3_expr(left,z3_vars) - get_z3_expr(right,z3_vars)

    if (expr.data == "select"):
        return get_select(expr, z3_vars)

    if (expr.data == "var"):
       return z3_vars[expr.children[0].value][0]
    else:
        # right could be a num
        return expr.children[0].value


def get_select(select_node, z3_vars):
    # returns array, index and isnumber
    array = select_node.children[0].children[0].value
    if (select_node.children[1].data == "num"):
        index = select_node.children[1].children[0].value
        return z3.Select(z3_vars[array][0], index)
    else:
        index = select_node.children[1].children[0].value
        return z3.Select(z3_vars[array][0], z3_vars[index][0])

def check_valid_variables(tree, src):
    """
    Function to check that all the valid variables are used in the program.
    """
    src_lines = src.split("\n")
    preconds = tree.children[0]
    declarations = tree.children[1]
    stmts = tree.children[2]
    postcond = tree.children[3]
    array_vars, integer_vars = get_vars(declarations)

    lst1 = verify_vars(preconds, array_vars, integer_vars)
    lst2 = verify_vars(stmts, array_vars, integer_vars)
    lst3 = verify_vars(postcond, array_vars, integer_vars)

    if lst1:
        print("Following errors found in precondition:")
        [print(src_lines[i.line-1] + " -- Line: "+ str(i.line) + "\n" + "^".rjust(i.column)) for i in lst1]
    if lst2:
        print("\nFollowing errors found in statements:")
        [print(src_lines[i.line-1] + " -- Line: "+ str(i.line) + "\n" + "^".rjust(i.column)) for i in lst2]
    if lst3:
        print("\nFollowing errors found in postcondition:")
        [print(src_lines[i.line-1] + " -- Line: "+ str(i.line) + "\n" + "^".rjust(i.column)) for i in lst3]

    return not (lst1 or lst2 or lst3)
        

def verify_vars(node, array_vars, integer_vars):
    """
    Verfies that the current node only uses the array vars and integers vars which were declared.
    """
    lst = []
    for child in node.find_data("var"):
        t = child.children[0].value in integer_vars
        if not t:
            lst.append(child)
    for child in node.find_data("array"):
        t = child.children[0].value in array_vars
        if not t:
            lst.append(child)
    return lst
    
def get_vars(declarations):
    """
    Return the variables which are declared
    """
    arrays = []
    integers = []
    for i in declarations.children:
        child = i.children[0]
        if child.data == "array":
            arrays.append(child.children[0].value)
        if child.data == "var":
            integers.append(child.children[0].value)
    return (arrays, integers)

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Error! Pass the file name (path) of the program!")
    else:
        src = open(sys.argv[1]).read()
        solve(src)