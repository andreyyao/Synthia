import z3
import lark
from z3.z3 import BitVec, BitVecVal, Const, ZeroExt

BITWIDTH = 16

GRAMMAR = """
?start: connect

?connect: cond
  | connect "|" cond      -> or
  | connect "^" cond      -> xor
  | connect "&" cond      -> and

?cond: sum
  | cond "!=" sum        -> ne
  | cond "==" sum        -> eq
  | cond "<" sum         -> lt
  | cond ">" sum         -> gt
  | "~" cond             -> not

?sum: term
  | cond "?" sum ":" sum -> if
  | sum "+" term         -> add
  | sum "-" term         -> sub


?term: item
  | term "*"  item      -> mul
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


def bitvec0():
    return BitVecVal(0, BITWIDTH)


def bitvec1():
    return BitVecVal(1, BITWIDTH)


def interp(tree, lookup):
    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr',
              'eq', 'ne', 'gt', 'lt', 'or', 'xor', 'and'):
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == 'add':
            return lhs + rhs
        elif op == 'sub':
            return lhs - rhs
        elif op == 'mul':
            return lhs * rhs
        elif op == 'shl':
            return lhs << rhs
        elif op == 'shr':
            return lhs >> rhs
        elif op == 'eq':
            return z3.If(lhs == rhs, bitvec1(), bitvec0())
        elif op == 'ne':
            return z3.If(lhs != rhs, bitvec1(), bitvec0())
        elif op == 'gt':
            return z3.If(lhs > rhs, bitvec1(), bitvec0())
        elif op == 'lt':
            return z3.If(lhs < rhs, bitvec1(), bitvec0())
        elif op == 'or':
            return lhs | rhs
        elif op == 'xor':
            return lhs ^ rhs
        elif op == 'and':
            return lhs & rhs
    elif op == 'neg':
        child = interp(tree.children[0], lookup)
        return - child
    elif op == 'num':
        return z3.BitVecVal(int(tree.children[0]), BITWIDTH)
    elif op == 'var':
        return lookup(tree.children[0])
    elif op == 'if':
        cond = interp(tree.children[0], lookup)
        true = interp(tree.children[1], lookup)
        false = interp(tree.children[2], lookup)
        return z3.If(cond != bitvec0(), true, false)
    elif op == 'not':
        child = interp(tree.children[0], lookup)
        return ~ child
