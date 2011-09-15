# DARhi abstract syntax tree node classes.
# Automatically generated from DARhi.asdl.

from darkitnode import \
    Symtab, Symbol, AST, \
    QUANT_NORMAL, QUANT_OPTIONAL, QUANT_LIST, QUANT_NONEMPTY

# Mapping from ASDL primitive type names to their PyObject equivalents.
primitive_types = {
    'identifier':   str,
    'int':          int,
    'string':       str,
    'bool':         bool,
    
    'symtab':       Symtab,
    'sym':          Symbol,
    
    'object':       object,
    
    'vsym':         Ellipsis,
    'fsym':         Ellipsis}

# Root of the language hierarchy.
class DARhiNode(AST):
    pass



class program(DARhiNode):
    _fields = []

class Program(program):
    _fields = [('decls', 'decl', QUANT_LIST),
               ('main', 'block', QUANT_OPTIONAL),
               ('scope', 'symtab', QUANT_NORMAL)]

class decl(DARhiNode):
    _fields = []

class VDecl(decl):
    _fields = [('id', 'vsym', QUANT_NORMAL)]

class FunctionDef(decl):
    _fields = [('id', 'fsym', QUANT_NORMAL),
               ('args', 'argument', QUANT_LIST),
               ('body', 'block', QUANT_NORMAL),
               ('scope', 'symtab', QUANT_NORMAL)]

class argument(DARhiNode):
    _fields = []

class Argument(argument):
    _fields = [('id', 'vsym', QUANT_NORMAL)]

class block(DARhiNode):
    _fields = []

class Block(block):
    _fields = [('stmtlist', 'stmt', QUANT_NONEMPTY)]

class pattern(DARhiNode):
    _fields = []

class PatTuple(pattern):
    _fields = [('elts', 'pattern', QUANT_LIST)]

class PatVar(pattern):
    _fields = [('id', 'vsym', QUANT_NORMAL),
               ('bnd', 'object', QUANT_NORMAL)]

class PatExpr(pattern):
    _fields = [('value', 'expr', QUANT_NORMAL)]

class PatIgnore(pattern):
    _fields = []

class patmatch(DARhiNode):
    _fields = []

class PatMatch(patmatch):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('iter', 'expr', QUANT_NORMAL)]

class PatMatchName(patmatch):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('iter', 'vsym', QUANT_NORMAL)]

class PatMatchLookup(patmatch):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('id', 'vsym', QUANT_NORMAL),
               ('key', 'expr', QUANT_NORMAL)]

class stmt(DARhiNode):
    _fields = []

class Return(stmt):
    _fields = [('value', 'expr', QUANT_OPTIONAL)]

class CallProc(stmt):
    _fields = [('func', 'fsym', QUANT_NORMAL),
               ('args', 'expr', QUANT_LIST)]

class Assign(stmt):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class SetUpdate(stmt):
    _fields = [('target', 'vsym', QUANT_NORMAL),
               ('op', 'updateop', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class RefUpdate(stmt):
    _fields = [('target', 'vsym', QUANT_NORMAL),
               ('op', 'updateop', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class Reinit(stmt):
    _fields = [('id', 'vsym', QUANT_NORMAL)]

class For(stmt):
    _fields = [('match', 'patmatch', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL),
               ('orelse', 'block', QUANT_OPTIONAL)]

class While(stmt):
    _fields = [('cond', 'expr', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL),
               ('orelse', 'block', QUANT_OPTIONAL)]

class PatWhile(stmt):
    _fields = [('match', 'patmatch', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL),
               ('orelse', 'block', QUANT_OPTIONAL)]

class If(stmt):
    _fields = [('cases', 'case', QUANT_NONEMPTY),
               ('orelse', 'block', QUANT_OPTIONAL)]

class InvDef(stmt):
    _fields = [('id', 'vsym', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class MapUpdate(stmt):
    _fields = [('target', 'vsym', QUANT_NORMAL),
               ('key', 'expr', QUANT_NORMAL),
               ('op', 'updateop', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class Pass(stmt):
    _fields = []

class Comment(stmt):
    _fields = [('text', 'string', QUANT_NORMAL)]

class case(DARhiNode):
    _fields = []

class CondCase(case):
    _fields = [('cond', 'expr', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL)]

class PatCase(case):
    _fields = [('match', 'patmatch', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL)]

class ApplCase(case):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL),
               ('body', 'block', QUANT_NORMAL)]

class expr(DARhiNode):
    _fields = []

class Name(expr):
    _fields = [('id', 'vsym', QUANT_NORMAL)]

class Num(expr):
    _fields = [('n', 'int', QUANT_NORMAL)]

class Str(expr):
    _fields = [('s', 'string', QUANT_NORMAL)]

class Bool(expr):
    _fields = [('b', 'object', QUANT_NORMAL)]

class Tuple(expr):
    _fields = [('elts', 'expr', QUANT_LIST)]

class BoolOp(expr):
    _fields = [('op', 'boolop', QUANT_NORMAL),
               ('values', 'expr', QUANT_LIST)]

class BinOp(expr):
    _fields = [('left', 'expr', QUANT_NORMAL),
               ('op', 'binop', QUANT_NORMAL),
               ('right', 'expr', QUANT_NORMAL)]

class UnaryOp(expr):
    _fields = [('op', 'unaryop', QUANT_NORMAL),
               ('operand', 'expr', QUANT_NORMAL)]

class Match(expr):
    _fields = [('match', 'patmatch', QUANT_NORMAL),
               ('scope', 'symtab', QUANT_NORMAL)]

class CallFunc(expr):
    _fields = [('func', 'fsym', QUANT_NORMAL),
               ('args', 'expr', QUANT_LIST)]

class Lookup(expr):
    _fields = [('id', 'vsym', QUANT_NORMAL),
               ('key', 'expr', QUANT_NORMAL)]

class CompatTuple(expr):
    _fields = [('pat', 'pattern', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class GetRefCount(expr):
    _fields = [('id', 'vsym', QUANT_NORMAL),
               ('value', 'expr', QUANT_NORMAL)]

class RelSetComp(expr):
    _fields = [('elt', 'expr', QUANT_NORMAL),
               ('enums', 'relenum', QUANT_NONEMPTY),
               ('conds', 'expr', QUANT_LIST),
               ('scope', 'symtab', QUANT_NORMAL)]

class relenum(DARhiNode):
    _fields = []

class RelEnum(relenum):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('iter', 'vsym', QUANT_NORMAL)]

class RelNegEnum(relenum):
    _fields = [('target', 'pattern', QUANT_NORMAL),
               ('iter', 'vsym', QUANT_NORMAL)]

class boolop(DARhiNode):
    _fields = []

class And(boolop):
    _fields = []

class Or(boolop):
    _fields = []

class binop(DARhiNode):
    _fields = []

class Add(binop):
    _fields = []

class Sub(binop):
    _fields = []

class Mult(binop):
    _fields = []

class Div(binop):
    _fields = []

class Mod(binop):
    _fields = []

class Eq(binop):
    _fields = []

class NotEq(binop):
    _fields = []

class Lt(binop):
    _fields = []

class LtE(binop):
    _fields = []

class Gt(binop):
    _fields = []

class GtE(binop):
    _fields = []

class In(binop):
    _fields = []

class NotIn(binop):
    _fields = []

class unaryop(DARhiNode):
    _fields = []

class Not(unaryop):
    _fields = []

class UAdd(unaryop):
    _fields = []

class USub(unaryop):
    _fields = []

class NotEmpty(unaryop):
    _fields = []

class Any(unaryop):
    _fields = []

class updateop(DARhiNode):
    _fields = []

class UpAdd(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

class UpRemove(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

class UpUnion(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

class UpDiff(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

class UpClear(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

class UpCopy(updateop):
    _fields = [('mod', 'object', QUANT_NORMAL)]

