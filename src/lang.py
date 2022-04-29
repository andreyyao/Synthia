import z3
import lark


GRAMMAR = """
?start: cond

?cond: sum
  | sum "==" sum        -> eq
  | sum ">" sum         -> gt
  | cond "||" cond      -> or
  | cond "&&" cond      -> and
  | "!" cond            -> not

?sum: term
  | sum "?" sum ":" sum -> if
  | sum "+" term         -> add
  | sum "-" term         -> sub


?term: item
  | term "*"  item      -> mul
  | term "/"  item      -> div
  | term ">>" item      -> shr
  | term "<<" item      -> shl

?item: NUMBER           -> num
  | "-" item            -> neg
  | CNAME               -> var
  | "(" start ")"

%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()

parser = lark.Lark(GRAMMAR)

def interp(tree, lookup):
    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr', 'eq', 'gt', 'or', 'and'):
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == 'add':
            return lhs + rhs
        elif op == 'sub':
            return lhs - rhs
        elif op == 'mul':
            return lhs * rhs
        elif op == 'div':
            return lhs / rhs
        elif op == 'shl':
            return lhs << rhs
        elif op == 'shr':
            return lhs >> rhs
        elif op == 'eq':
            return lhs == rhs
        elif op == 'gt':
            return (lhs > rhs) == 1
        elif op == 'or':
            return lhs | rhs
        elif op == 'and':
            return lhs & rhs
    elif op == 'neg':
        sub = interp(tree.children[0], lookup)
        return -sub
    elif op == 'num':
        return int(tree.children[0])
    elif op == 'var':
        return lookup(tree.children[0])
    elif op == 'if':
        cond = interp(tree.children[0], lookup)
        true = interp(tree.children[1], lookup)
        false = interp(tree.children[2], lookup)
        return (cond != 0) * true + (cond == 0) * false
    elif op == 'not':
        child = interp(tree.children[0], lookup)
        return (child == 0)
