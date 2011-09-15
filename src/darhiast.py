
import common
import darkitnode as dkn
import darkitast as dka
import darhinodes as dhn

class VSymbol(dka.Symbol):
    def __init__(self, *args, **kargs):
        super().__init__(*args, **kargs)

class FSymbol(dka.Symbol):
    pass

FLAG_INV = 'FLAG_INV'

class InvSymbol(VSymbol):
    def __init__(self, *args, flags = set(), **kargs):
        super().__init__(*args, flags = flags | {FLAG_INV}, **kargs)

dhn.primitive_types['vsym'] = VSymbol
dhn.primitive_types['fsym'] = FSymbol

dkn.do_NodeClassHackery(dhn)
from darhinodes import *

# Constants for pattern boundedness.
P_UNKNOWN = 'PATVAR_UNKNOWN'
P_UNBOUND = 'PATVAR_UNBOUND'
P_BOUND = 'PATVAR_BOUND'

# Modifiers on set updates.
UP_NONSTRICT = 'UP_NONSTRICT'
UP_STRICT = 'UP_STRICT'
UP_REFCOUNTED = 'UP_REFCOUNTED'



# --- Utilities. ---

def visitorChecker(visitor):
    """Decorator for verifying that a NodeVisitor only defines visit
    methods for existing nodes. Useful for finding dead code or misnamed
    methods."""
    for attr in visitor.__dict__:
        if attr.startswith('visit_'):
            nodename = attr[len('visit_'):]
            if nodename not in dhn.__dict__:
                raise common.InternalError(
                   'No node \'{}\' for \'{}\' to visit'.format(
                    nodename, visitor.__name__))
    return visitor

# These functions are convenient for categorizing nodes into
# one of two kinds, while asserting that it is not of any other kind.

# Test pattern boundedness. A pattern variable is either bound or unbound
# (or unknown, which is disallowed for this test). A pattern expression
# is always bound. A pattern tuple is bound or unbound if all of its
# components are the same way.

def isBoundPatVar(node):
    dka.assertnodetype(node, PatVar)
    if node.bnd is P_BOUND:
        return True
    elif node.bnd is P_UNBOUND:
        return False
    else: assert()

def isUnboundPat(node):
    if dka.hasnodetype(node, PatVar):
        return not isBoundPatVar(node)
    elif dka.hasnodetype(node, PatTuple):
        return all(isUnboundPat(elt) for elt in node.elts)
    elif dka.hasnodetype(node, PatExpr):
        return False
    else:
        assert()

def isBoundPat(node):
    if dka.hasnodetype(node, PatVar):
        return isBoundPatVar(node)
    elif dka.hasnodetype(node, PatTuple):
        return all(isBoundPat(elt) for elt in node.elts)
    elif dka.hasnodetype(node, PatExpr):
        return True
    else:
        assert()

# Other type-testing functions.

def isAddUpdate(node):
    """Test update type."""
    dka.assertnodetype(node, SetUpdate) 
    if dka.hasnodetype(node.op, UpAdd):
        return True
    elif dka.hasnodetype(node.op, UpRemove):
        return False
    else: assert()

def isPosEnum(node):
    """Test enumerator type."""
    dka.assertnodetype(node, {RelEnum, RelNegEnum})
    return dka.hasnodetype(node, RelEnum)

#def isPosEnum(node):
#    """Test enumerator type."""
#    if dka.hasnodetype(node, {Enum, AttrEnum}):
#        return True
#    elif dka.hasnodetype(node, {NegEnum, NegAttrEnum}):
#        return False
#    else: assert()

def isPatCase(node):
    """Test If case type."""
    if dka.hasnodetype(node, PatCase):
        return True
    elif dka.hasnodetype(node, CondCase):
        return False
    else: assert()

def isPatMatchName(node):
    """Test PatMatch type. This is really an implementation detail,
    to allow the same bit of code to work across different stages
    of the transformation."""
    if dka.hasnodetype(node, PatMatchName):
        return True
    elif dka.hasnodetype(node, PatMatch):
        return False
    else: assert()

def isPatMatchLookup(node):
    if dka.hasnodetype(node, PatMatchLookup):
        return True
    elif dka.hasnodetype(node, PatMatchName):
        return False
    else: assert()

def isAttrEnum(node):
    """Again, this is an implementation detail, testing whether we
    are dealing with AttrEnums or regular Enums."""
    if dka.hasnodetype(node, {Enum, NegEnum}):
        return False
    elif dka.hasnodetype(node, {AttrEnum, NegAttrEnum}):
        return True
    else: assert()

# Conversion utilities.

class PatternToValueConverter(dka.NodeVisitor):
    """Convert a pattern tuple tree to a structurally equivalent
    value tuple tree."""
    
    def run(self, node):
        dka.assertnodetype(node, pattern)
        return super().run(node)
    
    def visit_PatTuple(self, node):
        return Tuple([self.visit(elt) for elt in node.elts])
    
    def visit_PatVar(self, node):
        return Name(node.id)
    
    def visit_PatExpr(self, node):
        return node.value

def patternToValue(code):
    return PatternToValueConverter().runBoth(code)

class ValueToPatternConverter(dka.NodeVisitor):
    """Opposite of the above. This is not strictly a reversal
    since a PatExpr containing a Name would be turned into a
    Name, and then back into a PatVar instead of a PatExpr.
    Pattern boundedness is also set to unknown unless a default
    is requested."""
    
    def run(self, node, bnd = P_UNKNOWN):
        self.bnd = bnd
        return super().run(node)
    
    def generic_visit(self, node):
        return PatExpr(node)
    
    def visit_Tuple(self, node):
        return PatTuple([self.visit(elt) for elt in node.elts])
    
    def visit_Name(self, node):
        return PatVar(node.id, self.bnd)

def valueToPattern(code, bnd = P_UNKNOWN):
    return ValueToPatternConverter().runBoth(code, bnd)

class AttrToSelectorConverter(dka.NodeVisitor):
    """Convert a field access chain to a selector."""
    
    def generic_visit(self, node):
        assert()
    
    def visit_Name(self, node):
        return SelName(node.id)
    
    def visit_Attribute(self, node):
        return SelAttr(self.visit(node.value), node.attr)

def attrToSelector(code):
    return AttrToSelectorConverter().runBoth(code)

class SelectorToAttrConverter(dka.NodeVisitor):
    """Opposite of the above."""
    
    def generic_visit(self, node):
        assert()
    
    def visit_SelName(self, node):
        return Name(node.id)
    
    def visit_SelAttr(self, node):
        return Attribute(self.visit(node.path), node.attr)

def selectorToAttr(code):
    return SelectorToAttrConverter().runBoth(code)

def patmatchToNormal(patmatch):
    target = patmatch.target
    
    if dka.hasnodetype(patmatch, PatMatchName):
        iter = Name(patmatch.id)
    
    elif dka.hasnodetype(patmatch, PatMatchLookup):
        iter = Lookup(patmatch.id, dka.copy(patmatch.key))
    
    else: assert()
    
    return PatMatch(target, iter)

# Node generation.

def genBoundVar(id):
    return PatVar(id, P_BOUND)

def genUnboundVar(id):
    return PatVar(id, P_UNBOUND)

def genPatMatchSym(tupledomain, target, itersym):
    if not tupledomain:
        return PatMatch(target, Name(itersym))
    else:
        return PatMatchName(target, itersym)



# --- Visitors and transformers. ---

class PatternVisitor(dka.NodeVisitor):
    
    def generic_visit(self, node):
        dka.assertnodetype(node, pattern)
        super().generic_visit(node)
    
    def visit_PatTuple(self, node):
        self.generic_visit(node)
    
    def visit_PatVar(self, node):
        pass
    
    def visit_PatExpr(self, node):
        pass
    
    def visit_PatIgnore(self, node):
        pass

class StmtTransformerMixin(dka.BaseNodeVisitor):
    """This transformer allows statements to be inserted such that they are
    encountered just before the current node on all control-flow paths.
    Normally, this means inserting the new code just before the innermost
    statement node holding the current node. When the current node is in
    a loop condition or loop pattern match, code is inserted both before
    the loop and at the end of the body.
    
    This allows a transformer to, for example, replace a subexpression with
    a variable and insert code to make sure this variable is properly assigned
    a value."""
    
    # The user controls what code is added via the code_callback field.
    # This value is called when leaving a node to obtain the list of
    # statements that will be inserted. In loop conditions and pattern
    # matches, it is called twice, first for the prepended code and then
    # for the body's trailing code. In normal statements it is called once.
    # It is not called for non-statement nodes.
    
    # The code_callback value is saved in a stack, so that nested statements
    # (statements in the bodies of control structures) need not worry about
    # overwriting this value.
    
    # The methods setCode and addCode are provided as a sort of default behavior.
    # They make it easy to just supply lists of statements to insert.
    
    CCB_UNKNOWN = 'CCB_UNKNOWN'
    CCB_NORMAL = 'CCB_NORMAL'
    CCB_LOOP_ENTRY = 'CCB_LOOP_ENTRY'
    CCB_LOOP_REPEAT = 'CCB_LOOP_REPEAT'
    
    def __init__(self, *args, **kargs):
        super().__init__(*args, **kargs)
        
        self.code_callback = lambda ccb: []
        self.code_stack = []
    
    def setCode(self, code):
        assert(isinstance(code, list))
        incode = dka.copy(code)
        self.code_callback = lambda ccb: dka.copy(incode)
    
    def addCode(self, code):
        assert(isinstance(code, list))
        incode = dka.copy(code)
        last = self.code_callback(self.CCB_UNKNOWN)
        newcode = last + incode
        self.code_callback = lambda ccb: dka.copy(newcode)
    
    def push(self):
        self.code_stack.append(self.code_callback)
        self.code_callback = lambda ccb: []
    
    def pop(self):
        self.code_callback = self.code_stack.pop()
    
    def visit_stmt(self, node, *args, **kargs):
        # Save the previous code callback.
        self.push()
        
        # Handle this node.
        result = self.dispatch(node, transform_bypass = True, *args, **kargs)
        if result is None and self.transform_ignorenone:
            result = [node]
        else:
            result = dka.listifyValue(result)
        
        # Handle loop nodes. 
        if dka.hasnodetype(node, {For, While, PatWhile}):
            # Loop nodes can't be replaced by multiple statements,
            # since that would screw up our code insertion.
            assert(len(result) == 1)
            r = result[0]
            
            entrycode = self.code_callback(self.CCB_LOOP_ENTRY)
            # For pattern matches aren't allowed to change during the loop,
            # so we need only insert code to execute upon entering the loop.
            if not dka.hasnodetype(node, For):
                repeatcode = self.code_callback(self.CCB_LOOP_REPEAT)
                r.body.stmtlist.extend(repeatcode)
            newcode = entrycode + result
        
        # Handle normal nodes.
        else:
            precode = self.code_callback(self.CCB_NORMAL)
            newcode = precode + result
        
        # Restore the previous code callback.
        self.pop()
        
        return newcode

class GeneralStmtTransformer(dka.GeneralNodeTransformerMixin, StmtTransformerMixin, dka.WideNodeVisitor):
    pass

class StmtTransformer(dka.NodeTransformerMixin, StmtTransformerMixin, dka.WideNodeVisitor):
    pass



# --- Syntax generation. ---

#@visitorChecker
class SyntaxGenerator(dka.NodeVisitor):
    """Produce a concrete syntax representation of an AST."""
    
    # This dictionary gives a simple one-to-one translation
    # of some nodes to their symbols or names.
    simple_nodes = {
        'And':      'and',
        'Or':       'or',
        'Add':      '+',
        'Sub':      '-',
        'Mult':     '*',
        'Div':      '/',
        'Mod':      '%',
        'Not':      'not ',
        'UAdd':     '+',
        'USub':     '-',
        'Eq':       '==',
        'NotEq':    '!=',
        'Lt':       '<',
        'LtE':      '<=',
        'Gt':       '>',
        'GtE':      '>=',
        'In':       'in',
        'NotIn':    'not in',
        'NotEmpty': 'notempty ',
        'Any':      'any ',
        'UpAdd':    'add',
        'UpRemove': 'remove',
        'UpUnion':  'union',
        'UpDiff':   'diff',
        'UpClear':  'clear',
        'UpCopy' :  'copy'}
    
    # Indentation is tracked as an extra parameter to visit_*.
    # This is still passed to specializations that don't use it.
    
    def __init__(self, delim = '\n', tabs = True):
        """The delim specifier only applies to lists of separate pieces of code
        run at the same time (via runSeq). If tabs is an integer, tab characters
        are replaced with that many spaces."""
        super().__init__()
        self.delim = delim
        self.tabs = tabs
    
    def sym_text(self, node, sym):
        """This is a hook for subclasses to override."""
        return sym.name
    
    def run(self, node):
        result = self.visit(node, 0)
        if self.tabs is not True:
            assert(isinstance(self.tabs, int))
            result = result.replace('\t', ' ' * self.tabs)
        return result
    
    def runSeq(self, code):
        return self.delim.join(self.run(node) for node in code)
    
    def generic_visit(self, node, ind):
        """Lookup the strings for simple nodes; otherwise the node is unknown (i.e., bug)."""
        name = node.__class__._name
        if name in self.simple_nodes:
            return self.simple_nodes[name]
        else:
            return '<Unknown \'{}\'>'.format(name)
    
    def visit_Program(self, node, ind):
        decls = ''.join(self.visit(decl, 0) for decl in node.decls)
        # Start at indentation 0; first block will be at 1.
        main = self.visit(node.main, 0) \
               if node.main else ''
        return decls + '\n' + 'main:\n' + main
    
    def visit_VDecl(self, node, ind):
        return ('{}var {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.id)))
    
    def visit_Argument(self, node, ind):
        return self.sym_text(node, node.id)
    
    def visit_FunctionDef(self, node, ind):
        return ('\n{}def {}({}):\n{}'.format(
                '\t' * ind,
                self.sym_text(node, node.id),
                ', '.join(self.visit(a, ind) for a in node.args),
                self.visit(node.body, ind)))
    
    def visit_Block(self, node, ind):
        # Indentation level increases here as each block is processed.
        return ''.join(self.visit(s, ind + 1) for s in node.stmtlist)
    
    def visit_PatTuple(self, node, ind):
        return ('('
              + ', '.join(self.visit(c, ind) for c in node.elts)
              + (')' if len(node.elts) != 1 else ',)'))
    
    def visit_PatVar(self, node, ind):
        txt = ('?{}?' if node.bnd is P_UNKNOWN else
               '{}' if node.bnd is P_UNBOUND else
               '<{}>' if node.bnd is P_BOUND else
               '!?!')
        return txt.format(self.sym_text(node, node.id))
    
    def visit_PatExpr(self, node, ind):
        return '<{}>'.format(self.visit(node.value, ind))
    
    def visit_PatIgnore(self, node, ind):
        return '_'
    
    def visit_PatMatch(self, node, ind):
        return ('{} <- {}'.format(
                self.visit(node.target, ind),
                self.visit(node.iter, ind)))
    
    def visit_PatMatchName(self, node, ind):
        return ('{} <- {}'.format(
                self.visit(node.target, ind),
                self.sym_text(node, node.iter)))
    
    def visit_PatMatchLookup(self, node, ind):
        return ('{} <- {}[{}]'.format(
                self.visit(node.target, ind),
                self.sym_text(node, node.id),
                self.visit(node.key, ind)))
    
    def visit_Return(self, node, ind):
        return ('{}return{}\n'.format(
                '\t' * ind,
                ' ' + self.visit(node.value, ind)
                    if node.value else ''))
    
    def visit_CallProc(self, node, ind):
        return ('{}{}({})\n'.format(
                '\t' * ind,
                self.sym_text(node, node.func),
                ', '.join(self.visit(arg, ind) for arg in node.args)))
    
    
    def visit_Assign(self, node, ind):
        return ('{}{} = {}\n'.format(
                '\t' * ind,
                self.visit(node.target, ind),
                self.visit(node.value, ind)))
    
    def visit_SetUpdate(self, node, ind):
        if not dka.hasnodetype(node.op, UpClear):
            return ('{}{} {} {}\n'.format(
                    '\t' * ind,
                    self.sym_text(node, node.target),
                    self.visit(node.op, ind),
                    self.visit(node.value, ind)))
        else:
            return ('{}{} {}\n'.format(
                    '\t' * ind,
                    self.visit(node.op, ind),
                    self.sym_text(node, node.target)))
    
    def visit_RefUpdate(self, node, ind):
        # Should enforce this check someplace else.
        assert(dka.hasnodetype(node.op, {UpAdd, UpRemove}))
        return ('{}{} ref{} {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.target),
                '++' if dka.hasnodetype(node.op, UpAdd) else '--',
                self.visit(node.value, ind)))
    
    def visit_Reinit(self, node, ind):
        return ('{}new {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.id)))
    
    def visit_AttrUpdate(self, node, ind):
        return ('{}{}.{} = {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.target),
                node.attr,
                self.visit(node.value, ind)))
    
    def visit_DelAttr(self, node, ind):
        return ('{}delattr {}.{}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.target),
                node.attr))
    
    def visit_InvDef(self, node, ind):
        return ('{}{} === {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.id),
                self.visit(node.value, ind)))
    
    def visit_MapUpdate(self, node, ind):
        return ('{}{}[{}] {} {}\n'.format(
                '\t' * ind,
                self.sym_text(node, node.target),
                self.visit(node.key, ind),
                self.visit(node.op, ind),
                self.visit(node.value, ind)))
    
    def visit_For(self, node, ind):
        result = ('{}for {}:\n{}'.format(
                  '\t' * ind,
                  self.visit(node.match, ind),
                  self.visit(node.body, ind)))
        if node.orelse:
            result += ('{}else:\n{}'.format(
                       '\t' * ind,
                       self.visit(node.orelse, ind)))
        return result
    
    def visit_While(self, node, ind):
        result = ('{}while {}:\n{}'.format(
                  '\t' * ind,
                  self.visit(node.cond, ind),
                  self.visit(node.body, ind)))
        if node.orelse:
            result += ('{}else:\n{}'.format(
                       '\t' * ind,
                       self.visit(node.orelse, ind)))
        return result
    
    def visit_PatWhile(self, node, ind):
        result = ('{}while {}:\n{}'.format(
                  '\t' * ind,
                  self.visit(node.match, ind),
                  self.visit(node.body, ind)))
        if node.orelse:
            result += ('{}else:\n{}'.format(
                       '\t' * ind,
                       self.visit(node.orelse, ind)))
        return result
    
    def visit_If(self, node, ind):
        result = ''
        
        def el(c):
            return '' if c is node.cases[0] else 'el'
        
        for c in node.cases:
            
            if dka.hasnodetype(c, CondCase):
                result += ('{}{}if {}:\n{}'.format(
                           '\t' * ind,
                           el(c),
                           self.visit(c.cond, ind),
                           self.visit(c.body, ind)))
            
            elif dka.hasnodetype(c, PatCase):
                result += ('{}{}if {}:\n{}'.format(
                           '\t' * ind,
                           el(c),
                           self.visit(c.match, ind),
                           self.visit(c.body, ind)))
            
            elif dka.hasnodetype(c, ApplCase):
                result += ('{}{}if {} appliesto {}:\n{}'.format(
                            '\t' * ind,
                            el(c),
                            self.visit(c.target, ind),
                            self.visit(c.value, ind),
                            self.visit(c.body, ind)))
            
            else: assert()
        
        if node.orelse:
            result += ('{}else:\n{}'.format(
                       '\t' * ind,
                       self.visit(node.orelse, ind)))
        
        return result
    
    def visit_Pass(self, node, ind):
        return '{}pass\n'.format('\t' * ind)
    
    def visit_Comment(self, node, ind):
        return '{}# {}\n'.format('\t' * ind, node.text)
    
    def visit_Name(self, node, ind):
        return self.sym_text(node, node.id)
    
    def visit_Num(self, node, ind):
        return str(node.n)
    
    def visit_Str(self, node, ind):
        return '\'' + node.s + '\''
    
    def visit_Bool(self, node, ind):
        return str(node.b)
    
    def visit_Tuple(self, node, ind):
        return ('('
              + ', '.join(self.visit(e, ind) for e in node.elts)
              + (')' if len(node.elts) != 1 else ',)'))
    
    def visit_BoolOp(self, node, ind):
        return ((' ' + self.visit(node.op, ind) + ' ').join(
                self.visit(v, ind) for v in node.values))
    
    def visit_BinOp(self, node, ind):
        return (self.visit(node.left, ind) + ' '
              + self.visit(node.op, ind) + ' '
              + self.visit(node.right, ind))
    
    def visit_UnaryOp(self, node, ind):
        return (self.visit(node.op, ind) + self.visit(node.operand, ind))
    
    def visit_CallFunc(self, node, ind):
        return (self.sym_text(node, node.func)
              + '('
              + ', '.join(self.visit(a, ind) for a in node.args)
              + ')')
    
    def visit_Attribute(self, node, ind):
        return ('{}.{}'.format(
                self.visit(node.value, ind),
                node.attr))
    
    def visit_HasAttr(self, node, ind):
        return ('({} hasattr {})'.format(
                self.visit(node.value, ind),
                node.attr))
    
    def visit_Lookup(self, node, ind):
        return ('{}[{}]'.format(
                self.sym_text(node, node.id),
                self.visit(node.key, ind)))
    
    def visit_CompatTuple(self, node, ind):
        return ('{} compatiblewith {}'.format(
                self.visit(node.pat, ind),
                self.visit(node.value, ind)))
    
    def visit_Match(self, node, ind):
        return ('(? {})'.format(
                self.visit(node.match, ind)))
    
    def visit_Pick2nd(self, node, ind):
        return ('({}[[{}]])'.format(
                self.sym_text(node, node.id),
                self.visit(node.key, ind)))
    
    def visit_GetRefCount(self, node, ind):
        return ('{} getcount {}'.format(
                self.sym_text(node, node.id),
                self.visit(node.value, ind)))
    
    def visit_RelSetComp(self, node, ind):
        return ('{{{} : {}{}}}'.format(
                self.visit(node.elt, ind),
                ', '.join(self.visit(enum, ind) for enum in node.enums),
                ' | ' + ', '.join(self.visit(cond, ind) for cond in node.conds)
                  if len(node.conds) > 0 else ''))
    
    def visit_SetComp(self, node, ind):
        return ('{{{} : {}{}}}'.format(
                self.visit(node.elt, ind),
                ', '.join(self.visit(enum, ind) for enum in node.enums),
                ' | ' + self.visit(node.cond, ind) if node.cond else ''))
    
    def visit_Enum(self, node, ind):
        return ('{} in {}'.format(
                self.visit(node.target, ind),
                self.sym_text(node, node.iter)))
    
    def visit_NegEnum(self, node, ind):
        return ('{} not in {}'.format(
                self.visit(node.target, ind),
                self.sym_text(node, node.iter)))
    
    visit_RelEnum = visit_Enum
    visit_RelNegEnum = visit_NegEnum
    
    def visit_AttrEnum(self, node, ind):
        return ('{} in {}'.format(
                self.visit(node.target, ind),
                self.visit(node.iter, ind)))
    
    def visit_NegAttrEnum(self, node, ind):
        return ('{} not in {}'.format(
                self.visit(node.target, ind),
                self.visit(node.iter, ind)))
    
    def visit_SelName(self, node, ind):
        return self.sym_text(node, node.id)
    
    def visit_SelAttr(self, node, ind):
        return self.visit(node.path, ind) + '.' + node.attr
    
    def visit_UpAdd(self, node, ind):
        name = node.__class__._name
        mods = {UP_STRICT: '',
                UP_NONSTRICT: '-ns',
                UP_REFCOUNTED: '-rc'}
        
        return self.simple_nodes[name] + mods[node.mod]
    
    visit_UpRemove = visit_UpAdd
    visit_UpUnion = visit_UpAdd
    visit_UpDiff = visit_UpAdd
    visit_UpClear = visit_UpAdd
    visit_UpCopy = visit_UpAdd

def genSyntax(code, **kargs):
    return SyntaxGenerator(**kargs).runBoth(code)
