import lang
import z3
import sys

BITWIDTH = lang.BITWIDTH

def pretty(tree, subst={}, paren=True):
    """Pretty-print a tree, with optional substitutions applied.
    If `paren` is true, then loose-binding expressions are
    parenthesized. We simplify boolean expressions "on the fly."
    """

    # Add parentheses?
    def pars(s):
        if paren:
            return '({})'.format(s)
        else:
            return s

    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr',
              'eq', 'ne', 'gt', 'lt', 'and', 'xor', 'or'):
        lhs = pretty(tree.children[0], subst, True)
        rhs = pretty(tree.children[1], subst, True)
        c = {
            'add': '+',
            'sub': '-',
            'mul': '*',
            'div': '/',
            'shl': '<<',
            'shr': '>>',
            'eq' : '==',
            'ne' : '!=',
            'lt' : '<',
            'gt' : '>',
            'and': '&',
            'xor': '^',
            'or' : '|'
        }[op]
        return pars('{} {} {}'.format(lhs, c, rhs))
    elif op == 'neg':
        sub = pretty(tree.children[0], subst)
        return '-{}'.format(sub, True)
    elif op == 'not':
        child = pretty(tree.children[0], subst)
        return '~{}'.format(child, True)
    elif op == 'num':
        return tree.children[0]
    elif op == 'var':
        name = tree.children[0]
        return str(subst.get(name, name))
    elif op == 'if':
        cond = pretty(tree.children[0], subst)
        true = pretty(tree.children[1], subst)
        false = pretty(tree.children[2], subst)
        return pars('{} ? {} : {}'.format(cond, true, false))


def run(tree, env):
    """Ordinary expression evaluation.
    `env` is a mapping from variable names to values.
    """

    return lang.interp(tree, lambda n: env[n])
    

def z3_expr(tree, vars=None):
    """Create a Z3 expression from a tree.
    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width BITWIDTH. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, BITWIDTH)
            vars[name] = v
            return v

    return lang.interp(tree, get_var), vars


def model_values(model):
    """Get the values out of a Z3 model.
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }


def expand(hole, plain_vars):
    """ Expands a single hole to switches among {v1, ..., vn, h}
    where v1,...,vn are all the bound variables.
    """
    name = hole.decl().name()
    if name.startswith("hh"):
        expr = z3.BitVec(name + "#$num", BITWIDTH)
        for v in plain_vars:
            cond = z3.BitVec(name + "#" + v, BITWIDTH)
            expr = z3.If(cond != lang.bitvec0(),
                         expr, z3.BitVec(v, BITWIDTH))
        return expr
    else:
        return hole


def dig_holes(tree, plain_vars):
    """ Replaces each hole in tree with conditional switches
    between bound variables and constants"""
    if tree.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return expand(tree, plain_vars)
    else:
        substs = [(c, dig_holes(c, plain_vars)) for c in tree.children()]
        return z3.substitute(tree, substs)

    
def fill_holes(tree, model):
    """ Fills digged holes back in and returns new model_values """
    model_vals = model_values(model)

    # recursive constant folding from root of hole tree
    def fold_cond(t):
        decl = t.decl()
        if (decl.kind() == z3.Z3_OP_UNINTERPRETED
            and decl.name().endswith("$val")):
            return model_vals[decl.name()]
        elif decl.kind() == z3.Z3_OP_ITE:
            cond = t.children()[0]
            if cond.decl().kind() == z3.Z3_OP_DISTINCT:
                lhs = cond.children()[0]
                if (lhs.decl().kind() == z3.Z3_OP_UNINTERPRETED
                    and lhs.decl().name().startswith("hh")):
                    if model_vals[lhs.decl().name()].as_long() != 0:
                        return fold_cond(t.children()[1])
                    else:
                        return t.children()[2]
                else:
                    return t
            else:
                return t
        else:
            return t
        
    new_model_vals = { }

    for key in model_vals:
        if key.startswith("h") and not key.startswith("hh"):
            new_model_vals[key] = model_vals[key]

    def helper(t):
        if t.decl().kind() == z3.Z3_OP_ITE:
            cond = t.children()[0]
            false = t.children()[2]
            if (false.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and cond.children()[0].decl().name().startswith("hh")):
                # t is now Root of the manufactured hole tree
                # Start constant folding
                hole = cond.children()[0]
                key = hole.decl().name()[:hole.decl().name().index("#")]
                new_val = fold_cond(t)
                new_model_vals[key] = new_val
            else:
                for child in t.children():
                    helper(child)
        else:
            for child in t.children():
                helper(child)

    helper(tree)
    return new_model_vals
        

    
def solve(phi):
    """Solve a Z3 expression, returning the model.
    """

    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


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

    expr2 = dig_holes(expr2, plain_vars)

    print(expr2)

    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )

    # Solve the constraint.
    model = solve(goal)
    print(model)
    model_vals = fill_holes(expr2, model)
    return model_vals



def process(source):
    src1, src2 = source.strip().split('\n')

    parser = lang.parser# lark.Lark(lang.GRAMMAR)
    tree1 = parser.parse(src1)
    tree2 = parser.parse(src2)

    model_values = synthesize(tree1, tree2)
    print(pretty(tree1))
    print(pretty(tree2, model_values))
    print(model_values)

    
if __name__ == '__main__':
    process(sys.stdin.read())
