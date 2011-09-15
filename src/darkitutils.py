################################################################################
# darihutils.py: Utilities for transforming/implementing program features.     #
# Author: Jon Brandvein                                                        #
################################################################################

import common
import darkitast as dka
import darhiast as dha
import symtab as st

class UtilError(common.ProcessError):
    pass



# A symbol type for reference-counted sets.
#class RCSSymbol(dha.VSymbol):
#    pass

FLAG_REFCOUNTED = 'FLAG_REFCOUNTED'



def rebuildTree(tree):
    dka.checkTree(tree)
    try:
        st.buildSymtab(tree)
    except common.ProgramError as err:
        print('----')
        print(dha.genSyntax(tree))
        print('----')
        raise err

def genVDeclList(syms):
    """Create a list of variable declaraitons from a sequence of symbols."""
    sortedsyms = sorted(syms, key = lambda s: s.name)
    return [dha.VDecl(sym) for sym in sortedsyms]

def enumToClause(enum, body):
    """Generate a For or If clause (with the specified body)
    that corresponds to an enumerator."""
    ### Could use a little refactoring; break off AttrEnum stuff into separate method.
    if dha.isPosEnum(enum):
        if dha.isAttrEnum(enum):
            code = [dha.For(dha.PatMatch(dka.copy(enum.target),
                                         dha.selectorToAttr(enum.iter)),
                            body)]
        else:
            code = [dha.For(dha.PatMatchName(dka.copy(enum.target),
                                             enum.iter),
                            body)]
    else:
        if dha.isAttrEnum(enum):
            code = [dha.If([dha.CondCase(dha.BinOp(dha.patternToValue(enum.target),
                                                   dha.NotIn(),
                                                   dha.selectorToAttr(enum.iter)),
                                         body)])]
        else:
            code = [dha.If([dha.CondCase(dha.BinOp(dha.patternToValue(enum.target),
                                                   dha.NotIn(),
                                                   dha.Name(enum.iter)),
                                         body)])]
    return code

def enumsToClauses(enums, cond, body):
    code = body
    if cond:
        code = [dha.If([dha.CondCase(cond, dha.Block(code))])]
    for enum in reversed(enums):
        code = enumToClause(enum, dha.Block(code))
    return code

### Only TD for now
def enumsToClauses_reordered(enums, cond, body, boundsyms):
    
    ENUM = 'ENUM'
    COND = 'COND'
    
    boundsyms = set(boundsyms)
    
    alltargetsyms = set()
    
    enum_list = []
    
    for e in enums:
        targetsyms = set(st.gatherSymbols(e.target))
        alltargetsyms |= targetsyms
        unboundsyms = targetsyms - boundsyms
        
        isfield = (hasattr(e.iter, 'isfieldset') and
                   dka.hasnodetype(e.target, dha.PatTuple) and
                   len(e.target.elts) == 2 and
                   dka.hasnodetype(e.target.elts[0], dha.PatVar))
        isfieldfirst = e.target.elts[0].id if isfield else None
        
        if isfieldfirst is not None and isfieldfirst in boundsyms:
            unboundsyms = set()
        
        enum_list.append((e, targetsyms, unboundsyms, isfieldfirst))
    
    if cond:
        condhandled = False
        condsyms = set(st.gatherSymbols(cond)) & alltargetsyms
    
#    print('---')
#    for e, t, u in enum_list:
#        print(dha.genSyntax(e) + ': ' + ', '.join(s.name for s in t) +
#              ' (' + ', '.join(s.name for s in u) + ') ' + str(len(u)))
#    if cond:
#        print('condsyms: ' + ', '.join(s.name for s in condsyms))
#    print('---')
    
    sorted_clauses = []
    
    # Trying to add...
    # Hack heuristic: prefer orders that, when given the choice,
    # go up using the most recently added clause (depth first).
    
    def clauseorder(elem):
        return len(elem[2])
    
    while len(enum_list) > 0:
        if cond and not condhandled and len(condsyms) == 0:
            sorted_clauses.append((COND, cond))
            condhandled = True
        
        else:
            
            copyel = list(enumerate(enum_list))
            copyel.sort(key = lambda elem: clauseorder(elem[1]))
#            enum_list.sort(key = clauseorder)
            
#            e, ts, us, isff = enum_list[0]
            e, ts, us, isff = copyel[0][1]
            sorted_clauses.append((ENUM, e))
            
            for i, (e2, ts2, us2, isff2) in copyel[1:]:
                us2.difference_update(ts)
                if isff2 is not None and isff2 in ts:
                    us2.clear()
                if cond and not condhandled:
                    condsyms.difference_update(ts)
            
            enum_list.pop(copyel[0][0])
    if cond and not condhandled:
        sorted_clauses.append((COND, cond))
        condhandled = True
    
#    print('---')
#    for k, e in sorted_clauses:
#        print(k + ': ' + dha.genSyntax(e))
#    print('---')
    
    code = body
    for k, cl in reversed(sorted_clauses):
        if k is COND:
            code = [dha.If([dha.CondCase(cl, dha.Block(code))])]
        elif k is ENUM:
            code = enumToClause(cl, dha.Block(code))
        else: assert()
    return code

def desingletonize(node):
    dka.assertnodetype(node, {dha.Tuple, dha.PatTuple})
    return node if len(node.elts) != 1 else node.elts[0]

def genDTuple(elts):
    return desingletonize(dha.Tuple(elts))

def genDPatTuple(elts):
    return desingletonize(dha.PatTuple(elts))

def tuplematcher(left, right, bindings):
    if (dka.hasnodetype(left, dha.PatTuple) and
        dka.hasnodetype(right, dha.Tuple) and
        len(left.elts) == len(right.elts)):
        return all(tuplematcher(a, b, bindings)
                   for a, b in zip(left.elts, right.elts))
    elif dka.hasnodetype(left, dha.PatVar):
        if dka.hasnodetype(right, dha.Name):
            bindings[left.id] = right.id
            return True
        else:
            return False
    else:
        return False

def eliminatedecomp(decomp, code):
    dka.assertnodetype(decomp, dha.Assign)
    bindings = {}
    if tuplematcher(decomp.target, decomp.value, bindings):
        st.replaceSymbols(code, bindings)
        return code
    else:
        return [decomp] + code

class ApplCaseEliminator(dka.NodeTransformer):
    
    def visit_If(self, node):
        self.marker = node
        self.generic_visit(node)
        
        if not (len(node.cases) == 1 and
                dka.hasnodetype(node.cases[0], dha.ApplCase)):
            return
        case = node.cases[0]
        
        wipepat = wipePattern(dka.copy(case.target))
        assign = dha.Assign(dka.copy(case.target), dka.copy(case.value))
        
        bodycode = eliminatedecomp(assign, case.body.stmtlist)
        
        check = dha.CompatTuple(wipepat, dka.copy(case.value))
        newcase = dha.CondCase(check, dha.Block(bodycode))
        code = dha.If([newcase], node.orelse)
        
        return code
    
    def visit_ApplCase(self, node):
        if not (dka.getParentNode(node) is self.marker and
                dka.getParentIndex(node) == 0):
            assert()
        self.generic_visit(node)

def eliminateApplCase(code):
    ApplCaseEliminator().run(code)



dummysym = dha.VSymbol('_')

class PatternWiper(dka.NodeTransformer):
    def generic_visit(self, node):
        assert()
    
    def visit_PatTuple(self, node):
        return dha.PatTuple([self.visit(elt) for elt in node.elts])
    
    def visit_PatVar(self, node):
        return dha.genUnboundVar(dummysym)
    
    def visit_PatExpr(self, node):
        return dha.genUnboundVar(dummysym)
    
    def visit_PatIgnore(self, node):
        return dha.genUnboundVar(dummysym)

def wipePattern(pattree):
    return PatternWiper().run(pattree)

class PatternIgnorifier(dka.NodeTransformer):
    
    def run(self, node, keep):
        self.keep = keep
        return super().run(node)
    
    def generic_visit(self, node):
        assert()
    
    def visit_PatTuple(self, node):
        return dha.PatTuple([self.visit(elt) for elt in node.elts])
    
    def visit_PatVar(self, node):
        if node.id not in self.keep:
            return dha.PatIgnore()

def ignorify(pattree, keep):
    return PatternIgnorifier().run(pattree, keep)



class UseFinder(dka.NodeVisitor):
    
    def run(self, node):
        self.syms = set()
        super().run(node)
        return self.syms
    
    def generic_visit(self, node):
        for fieldinfo, value in dka.iter_fields(node):
            if fieldinfo.isSymbolField():
                self.syms.add(value)
        super().generic_visit(node)
    
    def visit_VDecl(self, node):
        super().generic_visit(node)
    
    def visit_SetUpdate(self, node):
        super().generic_visit(node)

class EliminateUnused(dka.GeneralNodeTransformer):
    
    def run(self, node, unneeded):
        self.unneeded = unneeded
        super().run(node)
    
    def visit_VDecl(self, node):
        if self.unneeded(node.id):
            return None
        else:
            return node
    
    def visit_SetUpdate(self, node):
        if self.unneeded(node.target):
            return None
        else:
            return node



# --- Update rewriting. ---

# Field and set update rewrites are object-domain;
# multiset rewrites are tuple-domain.

class SetUpdateRewriter(dka.NodeTransformer):
    """Rewrite non-strict add and remove updates as strict ones.
    Strict and reference-counted updates are ignored.
    Raises an error if other updates besides add and remove are found."""
    
    def visit_SetUpdate(self, node):
        isaddup = dha.isAddUpdate(node)
        
        if node.op.mod is not dha.UP_NONSTRICT:
            return
        
        has = dha.Match(dha.PatMatch(dha.valueToPattern(dka.copy(node.value)),
                                     dha.Name(node.target)),
                        dka.Symtab())
        if isaddup:
            test = dha.UnaryOp(dha.Not(), has)
        else:
            test = has
        
        newupdate = dka.copy(node)
        newupdate.op.mod = dha.UP_STRICT
        
        blk = dha.Block([newupdate])
        return dha.If([dha.CondCase(test, blk)])

def rewriteSetUpdates(tree):
    SetUpdateRewriter().run(tree)

## (For strictness)
#class FieldUpdateRewriter(dka.NodeTransformer):
#    def visit_AttrUpdate(self, node):
#        remupdate = [dha.DelAttr(node.target, node.attr)]
#        has = dha.HasAttr(dha.Name(node.target), node.attr)
#        rem = dha.If([dha.CondCase(has, dha.Block(remupdate))])
#        addupdate = dha.AttrUpdate(node.target, node.attr, node.value)
#        code = [rem, addupdate]
#        return code
#
#def rewriteFieldUpdates(tree):
#    FieldUpdateRewriter().run(tree)

class MultisetRewriter(dka.NodeTransformer):
    
    def run(self, node):
        self.multisyms = set()
        
        super().run(node)
        
        for s in self.multisyms:
            s.needsmulti = False
    
    def visit_SetUpdate(self, node):
        sym = node.target
        if hasattr(sym, 'needsmulti') and sym.needsmulti:
            self.multisyms.add(sym)
        else:
            return
        
        isaddup = dha.isAddUpdate(node)
        has = dha.Match(dha.PatMatchName(dha.valueToPattern(dka.copy(node.value)),
                                         node.target),
                        dka.Symtab())
        
        if isaddup:
            test1 = dha.UnaryOp(dha.Not(), has)
            inc1 = dha.RefUpdate(node.target, dka.copy(node.op), dka.copy(node.value))
            inc2 = dka.copy(inc1)
            
            body = dha.Block([dka.copy(node),
                              inc1])
            orelse = dha.Block([inc2])
            
            code = dha.If([dha.CondCase(test1, body)], orelse)
        
        else:
            test1 = has
            test2 = dha.BinOp(dha.GetRefCount(node.target, dka.copy(node.value)),
                              dha.Eq(),
                              dha.Num(0))
            body2 = dha.Block([dka.copy(node)])
            remif = dha.If([dha.CondCase(test2, body2)])
            body1 = [dha.RefUpdate(node.target, dka.copy(node.op), dka.copy(node.value)),
                     remif]
#            code = dha.If([dha.CondCase(test1, body1)])
            code = body1
        
        return code

def rewriteMultisets(tree):
    MultisetRewriter().run(tree)

def genClearCode(setsym, mod):
    """Generate code to empty a set."""
    v = st.getFreshNSymbol()
    match = dha.PatMatchName(dha.genUnboundVar(v), setsym)
    update = [dha.SetUpdate(setsym, dha.UpRemove(mod), dha.Name(v))]
    code = [dha.PatWhile(match, dha.Block(update))]
    return code

def genUnionDiffCode(leftsym, rightsym, isunion, mod):
    v = st.getFreshNSymbol()
    simpleop = dha.UpAdd(mod) if isunion else dha.UpRemove(mod)
    update = [dha.SetUpdate(leftsym, simpleop, dha.Name(v))]
    code = [dha.For(dha.PatMatchName(dha.genUnboundVar(v), rightsym),
                    dha.Block(update))]
    return code

def genCopyCode(leftsym, rightsym, mod):
    clear = genClearCode(leftsym, mod)
    copy = genUnionDiffCode(leftsym, rightsym, True, mod)
    return clear + copy

class BulkUpdateRewriter(dka.NodeTransformer):
    """Rewrite bulk updates in terms of elementary adds and removes.
    The update modifier (strict, non-strict, ref-counted) is not affected."""
    def visit_SetUpdate(self, node):
        op = node.op
        mod = op.mod
        
        # No change to addition and removal updates.
        if dka.hasnodetype(op, {dha.UpAdd, dha.UpRemove}):
            return
        
        elif dka.hasnodetype(op, {dha.UpUnion, dha.UpDiff}):
            isunion = dka.hasnodetype(op, dha.UpUnion)
            return genUnionDiffCode(node.target, node.value.id, isunion, mod)
        
        elif dka.hasnodetype(op, dha.UpClear):
            return genClearCode(node.target, mod)
        
        elif dka.hasnodetype(op, dha.UpCopy):
            return genCopyCode(node.target, node.value.id, mod)
        
        else: assert()

def rewriteBulkUpdates(tree):
    BulkUpdateRewriter().run(tree)
