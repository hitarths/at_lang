import lark
import z3
import sys

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
    | "if (" assertion ")" "then do {" equalitystmt* "}" elseblock?  -> if

elseblock: "else {" equalitystmt* "}" -> else
                                            //add while and for loop here    
postcond: "@post(" assertion ");"           //post condition
assertion: equality
        | smaller
        | z3_assertion                       
        | "(" assertion "and" assertion ")" -> and
        | "(" assertion "or" assertion ")"  -> or
        | "(" "not" assertion ")"           -> not

z3_assertion: "{:" /[^ ]+/ ":}"
equalitystmt : var "=" var ";"  -> equality
    |   var "=" NUMBER ";"  -> equality
    |   select "=" varnum ";" -> equality
    |   var "=" select ";" -> equality
    |   select "=" select ";" ->equality


equality: var "=" var
    |   var "=" varnum
    |   select "=" varnum  
    |   var "=" select
    |   select "=" select

smaller: var "<" var
    |   var "<" NUMBER

var: WORD
array: WORD
varnum: var
    | NUMBER    -> num
select: array "[" varnum "]" 


%import common.NUMBER
%import common.WORD
%import common.WS
%import common.CNAME
%ignore WS
""".strip()


def interp(tree, lookup):
    """Evaluate the arithmetic expression.
    Pass a tree as a Lark `Tree` object for the parsed expression. For
    `lookup`, provide a function for mapping variable names to values.
    """
    return
    


def run(tree, env):
    """Ordinary expression evaluation.
    `env` is a mapping from variable names to values.
    """

    return interp(tree, lambda n: env[n])


def z3_expr(tree, vars=None):
    """Create a Z3 expression from a tree.
    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width 8. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            return v

    return interp(tree, get_var), vars


def solve(phi):
    """Solve a Z3 expression, returning the model.
    """

    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


def model_values(model):
    """Get the values out of a Z3 model.
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }


def synthesize(tree1, tree2):
    """Given two programs, synthesize the values for holes that make
    them equal.
    `tree1` has no holes. In `tree2`, every variable beginning with the
    letter "h" is considered a hole.
    """
    expr1, vars1 = z3_expr(tree1)
    expr2, vars2 = z3_expr(tree2, vars1)
    # Filter out the variables starting with "h" to get the non-hole
    # variables.
    plain_vars = {k: v for k, v in vars1.items()
                  if not k.startswith('h')}
    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )
    # Solve the constraint.
    return solve(goal)

tree = None
def program_to_ssa():
    global tree
    src1 = """@pre( (((arr[0] = i and i=j) or j=0) and arr[0] = arr[i]));
    int a;
    int i;
    int b;
    int j;
    int[] arr;
    a = 4;
    arr[a] = 4;
    arr[50] = a;
    a = b;
    b = 324;
    if (a=4) then do {a=6;} else {a=90; a= 11; arr[a] = 43;}
    @post(i=j);
    """
    parser = lark.Lark(GRAMMAR, propagate_positions=True)
    tree = parser.parse(src1)

    preconds = tree.children[0]
    declarations = tree.children[1]
    stmts = tree.children[2]
    postcond = tree.children[3]
    global array_vars, integer_vars
    array_vars, integer_vars = get_vars(declarations)

    all_vars = array_vars + integer_vars
    for i in set(all_vars):
        if all_vars.count(i) != 1:
            print("The variable '{}' is declared more than once!".format(i))
            return

    if check_valid_variables(tree, src1):
        print("Program is syntactically correct!")
    else: 
        return "Exiting..."

    global z3_vars
    z3_vars= {var:z3.Int("{}_0".format(var)) for var in integer_vars}
    z3_vars.update({
        arr:z3.Array("{}_0".format(arr), z3.IntSort(), z3.IntSort()) for arr in array_vars
        })

    precond_z3 = get_z3_cond(preconds.children[0], integer_vars, array_vars, z3_vars)
    ## we got the procond
    print(precond_z3)

    ## Now we shall convert the program to SSA using following points:
    ## 1. We have to maintain a dictionary which tells us the latest numbering of a variable
    ## 2. For left side of any assignment we will use the current variable name, and on the right side we have to use
    ##    the new variable name which will be indexed by successor of the current index.
    ## 3. Only those variables will be updated in dictionary which are on right side. 
    ## 4. For the right side of an assignment we will use the updated dictionary variables.
    z3_stmt = []
    for stmt_node in stmts.children:
        z3_stmt.append((get_z3_statement(stmt_node), stmt_node))

    #check all the variables are correct.

def get_z3_statement(stmt_node):
    if (stmt_node.data == "assignment"):

    elif (stmt_node.data == "if"):
        pass
    else:
        # add more type of statements here.
        pass

def get_left_right_for_equality_statement(left, right, z3_vars):
    if (left.data == "select"):
        left = get_select(left, z3_vars)
    else:
        #left must be a var
        left = z3_vars[left.children[0].value]
    if (right.data == "select"):
        right = get_select(right, z3_vars)
    elif (right.data == "var"):
        right = z3_vars[right.children[0].value]
    elif (right.data == "varnum"):
        if (right.children[0].data == "var"):
            right = z3_vars[right.children[0].children[0].value]
        else:
            right = right.children[0].value
    else:
        # right could be a num
        right = right.children[0].value
    return (left,right)


def get_z3_cond(node, integer_vars, array_vars, z3_vars):

    def get_z3_cond_in(child):
        return get_z3_cond(child, integer_vars, array_vars, z3_vars)

    if node.data == "assertion":
        return get_z3_cond_in(node.children[0])
    if node.data == 'and':
        return z3.And(get_z3_cond_in(node.children[0]), get_z3_cond_in(node.children[1]))
    if node.data == "or":
        return z3.Or(get_z3_cond_in(node.children[0]), get_z3_cond_in(node.children[1]))
    if node.data == "not":
        return z3.Not(get_z3_cond_in(node.children[0]))
    if node.data == "equality":
        left = node.children[0]
        right = node.children[1]
        zleft, zright = get_left_right_for_equality(left,right, z3_vars)
        return (zleft == zright)
    if node.data == "smaller":
        left = node.children[0]
        right = node.children[1]
        zleft, zright = get_left_right_for_equality(left,right, z3_vars)
        return (left < right)

def get_left_right_for_equality(left, right, z3_vars):
    if (left.data == "select"):
        left = get_select(left, z3_vars)
    else:
        #left must be a var
        left = z3_vars[left.children[0].value]
    if (right.data == "select"):
        right = get_select(right, z3_vars)
    elif (right.data == "var"):
        right = z3_vars[right.children[0].value]
    elif (right.data == "varnum"):
        if (right.children[0].data == "var"):
            right = z3_vars[right.children[0].children[0].value]
        else:
            right = right.children[0].value
    else:
        # right could be a num
        right = right.children[0].value
    return (left,right)


def get_select(select_node, z3_vars):
    # returns array, index and isnumber
    array = select_node.children[0].children[0].value
    if (select_node.children[1].data == "num"):
        index = select_node.children[1].children[0].value
        return z3.Select(z3_vars[array], index)
    else:
        index = select_node.children[1].children[0].children[0].value
        return z3.Select(z3_vars[array], z3_vars[index])

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
    for child in node.find_data("varnum"):
        t = child.children[0].children[0].value in integer_vars
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
    program_to_ssa()