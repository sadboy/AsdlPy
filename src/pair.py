
import itertools
import collections

import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du
import computils as cu
import pattern as pat

class MSymbol(dha.VSymbol):
    def __init__(self, *args, **kargs):
        super().__init__(*args, fixset = True, **kargs)

class MetaMember(MSymbol):
    def __init__(self, *, id = None, t = None):
        self.id = id
        super().__init__('member' + ('_' + id if id is not None else ''),
                         t = t)

class MetaField(MSymbol):
    def __init__(self, attr, *, id = None, t = None):
        self.attr = attr
        self.id = id
        self.isfieldset = True
        super().__init__('field_' + attr + ('_' + id if id is not None else ''),
                         t = t)

def ismeta(sym):
    assert(isinstance(sym, dka.Symbol))
    return isinstance(sym, MSymbol)

def ismember(sym):
    assert(isinstance(sym, dka.Symbol))
    return isinstance(sym, MetaMember)

def isfield(sym):
    assert(isinstance(sym, dka.Symbol))
    return isinstance(sym, MetaField)



# --- Forward pair domain conversion. ---

### TODO: should assert that affected objects are not fixsets
class FieldPDEnterer(dka.NodeTransformer):
    
    def getFieldSym(self, attr, t1):
        if not attr in self.fielddict:
            sym = MetaField(attr)
            self.fielddict[attr] = sym
        else:
            sym = self.fielddict[attr]
        
        return sym
    
    def run(self, node):
        self.root = node
        self.fielddict = dict()
        self.incomp = False
        super().run(node)
    
    def visit_Program(self, node):
        self.generic_visit(node)
        
        node.decls[:0] = [dha.VDecl(fs)
                          for fs in self.fielddict.values()]
    
    def visit_AttrUpdate(self, node):
        self.generic_visit(node)
        
        fs = self.getFieldSym(node.attr, node.target.t)
        code = dha.SetUpdate(fs, dha.UpAdd(), dha.Tuple([dha.Name(node.target),
                                                         node.value]))
        return code
    
    def visit_Attribute(self, node):
        # Under normal circumstances, replace with a lookup into
        # the appropriate field metaset.
        if not self.incomp:
            self.generic_visit(node)
            
            fs = self.getFieldSym(node.attr, node.value._t)
            code = dha.Pick2nd(fs, node.value)
            return code
        
        # In comprehension result or condition expressions, replace with
        # the appropriate pair-domain variable.
        else:
            # ... in a post-traversal manner.
            self.generic_visit(node)
            dka.assertnodetype(node.value, dha.Name)
            v = self.fieldvar_helper(node.value.id, node.attr)
            return dha.Name(v)
    
    def visit_HasAttr(self, node):
        self.generic_visit(node)
        fs = self.getFieldSym(node.attr, node.value._t)
        tup = dha.PatTuple([dha.PatExpr(node.value),
                            dha.genUnboundVar(st.getFreshNSymbol())])
        return dha.Match(dha.PatMatchName(tup, fs), dka.Symtab())
    
    def visit_DelAttr(self, node):
        self.generic_visit(node)
        fs = self.getFieldSym(node.attr, node.target.t)
        code = dha.SetUpdate(fs, dha.UpRemove(),
                             dha.Tuple([dha.Name(node.target),
                                        dha.Pick2nd(fs, dha.Name(node.target))]))
        return code
    
    def fieldvar_helper(self, accpath, attr):
        """Take in an access path and attribute, and return the pair-domain
        symbol that replaces it. If the symbol is new, add a fieldenum entry
        for it."""
        term = (accpath, attr)
        if term not in self.fieldvars:
            name = accpath.name + '_' + attr
            # Hack.
            v = dha.VSymbol(name,
                            t = ('@', accpath.t, attr))
            self.fieldvars[term] = v
            self.fieldenums.append((term, v, accpath.t))
        else:
            v = self.fieldvars[term]
        return v
    
    def fieldenums_helper(self):
        """Generate actual enumerators for the fieldenums list, then
        clear the fieldenums list."""
        newenums = [dha.AttrEnum(dha.PatTuple([dha.genBoundVar(id),
                                               dha.genUnboundVar(v)]),
                                 dha.SelName(self.getFieldSym(attr, t)))
                    for (id, attr), v, t in self.fieldenums]
        self.fieldenums = []
        return newenums
    
    def visit_SetCompDef(self, node):
        compnode = node.comp
        
        self.incomp = True
#        self.p_uid = common.UID()
        self.fieldvars = {}
        self.fieldenums = []
        
        # Handle enumerators.
        for enum in compnode.enums:
            self.visit(enum)
        
        # Handle conditions and result expression.
        if compnode.cond:
            self.visit(compnode.cond)
        self.visit(compnode.elt)
        newenums = self.fieldenums_helper()
        compnode.enums.extend(newenums)
        
        self.incomp = False
    
    def visit_SelAttr(self, node):
        self.generic_visit(node)
        dka.assertnodetype(node.path, dha.SelName)
        v = self.fieldvar_helper(node.path.id, node.attr)
        newnode = dha.SelName(v)
        newnode._t = v.t
        return newnode
    
    def visit_AttrEnum(self, node):
        self.fieldenums = []
        self.generic_visit(node)
        dka.assertnodetype(node.iter, dha.SelName)
        
        et = dha.AttrEnum if dha.isPosEnum(node) else dha.NegAttrEnum
        e = et(node.target, dha.SelName(node.iter.id))
        
        newenums = self.fieldenums_helper()
        
        return newenums + [e]
    
    visit_NegAttrEnum = visit_AttrEnum

class MemberPDEnterer(dka.NodeTransformer):
    
    def getMemSym(self, t1):
        if None not in self.memdict:
            sym = MetaMember()
            self.memdict[None] = sym
        else:
            sym = self.memdict[None]
        
        return sym
    
    def run(self, node):
        self.counter = common.UID()
        self.memdict = dict()
        super().run(node)
    
    def visit_Program(self, node):
        self.generic_visit(node)
        node.decls[:0] = [dha.VDecl(sym)
                          for sym in self.memdict.values()]
    
    def visit_PatMatch(self, node):
        self.generic_visit(node)
        
        if (dka.hasnodetype(node.iter, dha.Name) and
            dha.isfixset(node.iter.id)):
            elem = self.visit(node.target)
            return dha.PatMatchName(elem, node.iter.id)
        
        cont = dha.valueToPattern(node.iter, dha.P_BOUND)
        elem = self.visit(node.target)
        return dha.PatMatchName(dha.PatTuple([cont, elem]),
                                self.getMemSym(elem._t))
    
    def visit_SetUpdate(self, node):
        if isinstance(node.target, MSymbol):
            return
        if dha.isfixset(node.target):
            return
        
        op = dha.UpAdd() if dha.isAddUpdate(node) else dha.UpRemove()
        cont = dha.Name(node.target)
        elem = self.visit(node.value)
        return dha.SetUpdate(self.getMemSym(elem._t),
                             op, dha.Tuple([cont, elem]))
    
    def visit_AttrEnum(self, node):
        dka.assertnodetype(node.iter, dha.SelName)
        ssym = node.iter.id
        et = dha.Enum if dha.isPosEnum(node) else dha.NegEnum
        
        if (isinstance(ssym, MSymbol) or
            dha.isfixset(ssym)):
            return et(node.target, ssym)
        
        iter = dha.genBoundVar(ssym)
        target = self.visit(node.target)
        
        return et(dha.PatTuple([iter, target]),
                  self.getMemSym(target._t))
    
    visit_NegAttrEnum = visit_AttrEnum

class TDResetter(dka.NodeVisitor):
    
    def visit_SetCompDef(self, node):
        node.id.info.td = True
        node.id.info.updateCompInfo()

def enterPairDomain(tree):
    FieldPDEnterer().run(tree)
    du.rebuildTree(tree)
    
    MemberPDEnterer().run(tree)
    du.rebuildTree(tree)
    
    TDResetter().run(tree)
    du.rebuildTree(tree)



# --- Backward pair-domain conversion. ---

def isforward(auxsym):
    return (pat.isauxmap(auxsym) and
            dha.isBoundPat(auxsym.pat.elts[0]) and
            dha.isUnboundPat(auxsym.pat.elts[1]))

def isforwardmember(auxsym):
    return isforward(auxsym) and ismember(auxsym.host)

def isforwardfield(auxsym):
    return isforward(auxsym) and isfield(auxsym.host)

def ismemberaux(auxsym):
    return pat.isauxmap(auxsym) and ismember(auxsym.host)

def isfieldaux(auxsym):
    return pat.isauxmap(auxsym) and isfield(auxsym.host)

def matchpair(pair):
    dka.assertnodetype(pair, {dha.Tuple, dha.PatTuple})
    assert(len(pair.elts) == 2)
    return pair.elts[0], pair.elts[1]

#def isforward(pair):
#    return (dha.isBoundPat(pair.elts[0]) and
#            dha.isUnboundPat(pair.elts[1]))
#
#def isbound(pair):
#    return (dha.isBoundPat(pair.elts[0]) and
#            dha.isBoundPat(pair.elts[1]))

class FieldPDLeaver(dka.NodeTransformer):
    
    def visit_For(self, node):
        self.generic_visit(node)
        
        match = node.match
        if dka.hasnodetype(match, dha.PatMatch):
            return
        ssym = match.id
        
        if isfield(ssym):
            attr = ssym.attr
        elif isfieldaux(ssym):
            attr = ssym.host.attr
        else: assert()
        
        if isforwardfield(ssym):
            cont, val = match.key, match.target
            has = dha.HasAttr(cont, attr)
            bind = dha.Assign(val, dha.Attribute(dka.copy(cont), attr))
            newbody = dha.Block([bind] + node.body.stmtlist)
            return dha.If([dha.CondCase(has, newbody)], node.orelse)
        else:
            newmatch = dha.patmatchToNormal(node.match)
            return dha.For(newmatch, node.body, node.orelse)
    
    def visit_BinOp(self, node):
        self.generic_visit(node)
        
        op = node.op
        
        if dka.hasnodetype(op, {dha.In, dha.NotIn}):
            
            if dka.hasnodetype(node.right, dha.Name):
                ssym = node.right.id
                
                if not isfield(ssym):
                    return node
                attr = ssym.attr
                
                cont, val = matchpair(node.left)
                has = dha.HasAttr(cont, attr)
                matches = dha.BinOp(dha.Attribute(dka.copy(cont), attr),
                                    dha.Eq(),
                                    val)
                cond = dha.BoolOp(dha.And(), [has, matches])
                
                if dka.hasnodetype(op, dha.NotIn):
                    cond = dha.Not(cond)
                
                return cond
        
        return node
    
    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        
        op = node.op
        operand = node.operand
        
        if dka.hasnodetype(op, dha.NotEmpty):
            if dka.hasnodetype(operand, dha.Lookup):
                if isforwardfield(operand.id):
                    attr = operand.id.host.attr
                    has = dha.HasAttr(operand.key, attr)
                    return has
        
        elif dka.hasnodetype(op, dha.Any):
            if dka.hasnodetype(operand, dha.Lookup):
                if isforwardfield(operand.id):
                    attr = operand.id.host.attr
                    return dha.Attribute(operand.key, attr)
        
        return node
    
    def visit_SetUpdate(self, node):
        self.generic_visit(node)
        
        ssym = node.target
        if isfield(ssym):
            attr = ssym.attr
            
            cont, val = matchpair(dka.copy(node.value))
            dka.assertnodetype(cont, {dha.Name, dha.PatVar})
            
            if dha.isAddUpdate(node):
                newnode = dha.AttrUpdate(cont.id, attr, val)
            else:
                newnode = dha.DelAttr(cont.id, attr)
            
            return [newnode, node]
        
        return node
    
    
#    def run(self, node):
#        self.incomp = False
#        super().run(node)
#    
#    def visit_For(self, node):
#        self.generic_visit(node)
#        match = node.match
#        target = match.target
#        iter = match.iter
#        
#        if not dka.hasnodetype(iter, dha.Name):
#            return
#        ssym = iter.id
#        
#        if not isfield(ssym):
#            return
#        
#        if not (isforward(target) or isbound(target)):
#            return
#        
#        cont, val = matchpair(target)
#        attr = ssym.attr
#        
#        cont1 = dha.patternToValue(cont)
#        cont2 = dka.copy(cont1)
#        val1 = dha.patternToValue(val)
#        has = dha.HasAttr(cont1, attr)
#        
#        if isforward(target):
#            bind = dha.Assign(val, dha.Attribute(cont2, attr))
#            newbodycode = [bind]
#            newbodycode.extend(node.body.stmtlist)
#            cond = dha.CondCase(has, dha.Block(newbodycode))
#            
#            if dka.hasnodetype(node, {dha.For, dha.PatWhile}):
#                newnode = dha.If([cond], node.orelse)
#            elif dka.hasnodetype(node, dha.PatCase):
#                newnode = cond
#            return newnode
#        
#        elif isbound(target):
#            matches = dha.BinOp(dha.Attribute(cont2, attr), dha.Eq(), val1)
#            test = dha.BoolOp(dha.And(), [has, matches])
#            cond = dha.CondCase(test, node.body)
#            
#            if dka.hasnodetype(node, {dha.For, dha.PatWhile}):
#                newnode = dha.If([cond], node.orelse)
#            elif dka.hasnodetype(node, dha.PatCase):
#                newnode = cond
#            return newnode
#    
#    visit_PatWhile = visit_PatCase = visit_For
#    
#    def visit_SetUpdate(self, node):
#        self.generic_visit(node)
#        
#        if not isfield(node.target):
#            return
#        
#        cont, val = matchpair(dka.copy(node.value))
#        attr = node.target.attr
#        
#        if dha.isAddUpdate(node):
#            newnode = dha.AttrUpdate(cont.id, attr, val)
#        else:
#            newnode = dha.DelAttr(cont.id, attr)
#        
#        return [newnode, node]
#    
#    def visit_Match(self, node):
#        self.generic_visit(node)
#        
#        iter = node.match.iter
#        if not dka.hasnodetype(iter, dha.Name):
#            return
#        ssym = iter.id
#        if not isfield(ssym):
#            return
#        
#        if not isforward(node.match.target):
#            return
#        
#        attr = ssym.attr
#        cont, val = matchpair(node.match.target)
#        
#        return dha.HasAttr(dha.patternToValue(cont), attr)
#    
#    def visit_Pick2nd(self, node):
#        self.generic_visit(node)
#        
#        if not isfield(node.id):
#            return
#        attr = node.id.attr
#        
#        return dha.Attribute(node.key, attr)
#    
#    def visit_Name(self, node):
#        if self.incomp:
#            if node.id in self.fieldvars:
#                return dka.copy(self.fieldvars[node.id])
#    
#    def visit_PatVar(self, node):
#        if self.incomp:
#            if node.id in self.fieldvars:
#                return dka.copy(dha.valueToPattern(self.fieldvars[node.id]))
#    
##    def visit_SetComp(self, node):
##        self.incomp = True
##        self.fieldvars = {}
##        newenums = []
##        for enum in node.enums:
##            ssym = enum.iter
##            if isfield(ssym):
##                attr = ssym.attr
##                cont, elem = matchpair(enum.target)
##                dka.assertnodetype(elem, dha.PatVar)
##                assert(elem.id not in self.fieldvars)
##                self.fieldvars[elem.id] = dha.Attribute(dha.patternToValue(cont), attr)
##            else:
##                newenums.append(enum)
##        node.enums = newenums
##        
##        for key1, value1 in self.fieldvars.items():
##            for key2, value2 in self.fieldvars.items():
##                if key2 == key1:
##                    continue
##                self.fieldvars[key2] = st.expandSymbols(value2, {key1: value1})
##        
##        self.generic_visit(node)
##        
##        self.incomp = False
##    
##    def visit_Enum(self, node):
##        et = dha.AttrEnum if dha.isPosEnum(node) else dha.NegAttrEnum
##        target = self.visit(node.target)
##        if node.iter in self.fieldvars:
##            iter = dha.attrToSelector(dka.copy(self.fieldvars[node.iter]))
##        else:
##            iter = dha.SelName(node.iter)
##        return et(target, iter)
##    
##    visit_NegEnum = visit_Enum

class MemberPDLeaver(dka.NodeTransformer):
    
    def visit_For(self, node):
        self.generic_visit(node)
        
        match = node.match
        ssym = match.id
        
        if isfield(ssym) or isfieldaux(ssym):
            return node
        
        if isforwardmember(ssym):
            newmatch = dha.PatMatch(match.target, match.key)
        else:
            newmatch = dha.patmatchToNormal(node.match)
        
        return dha.For(newmatch, node.body, node.orelse)
    
    def visit_BinOp(self, node):
        self.generic_visit(node)
        
        op = node.op
        
        if dka.hasnodetype(op, {dha.In, dha.NotIn}):
            
            if dka.hasnodetype(node.right, dha.Name):
                ssym = node.right.id
                
                if isfield(ssym):
                    return node
                
                if ismember(ssym):
                    cont, val = matchpair(node.left)
                    return dha.BinOp(val, op, cont)
        
        return node
    
    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        
        op = node.op
        operand = node.operand
        
        if dka.hasnodetype(op, dha.NotEmpty):
            if dka.hasnodetype(operand, dha.Lookup):
                if isforwardmember(operand.id):
                    return dha.UnaryOp(dha.NotEmpty(), operand.key)
        
        elif dka.hasnodetype(op, dha.Any):
            if dka.hasnodetype(operand, dha.Lookup):
                if isforwardmember(operand.id):
                    return dha.UnaryOp(dha.Any(), operand.key)
        
        return node
    
    def visit_SetUpdate(self, node):
        self.generic_visit(node)
        
        ssym = node.target
        if ismember(ssym):
            cont, val = matchpair(dka.copy(node.value))
            dka.assertnodetype(cont, {dha.Name, dha.PatVar})
            newnode = dha.SetUpdate(cont.id, dka.copy(node.op), val)
            return [newnode, node]
        
        return node
    
    
#    def visit_PatMatchName(self, node):
#        self.generic_visit(node)
#        
#        ssym = node.id
#        if (ismember(ssym) and
#            (isforward(node.target) or isbound(node.target))):
#            cont, elem = matchpair(node.target)
#            newnode = dha.PatMatch(elem, dha.patternToValue(cont))
#            return newnode
#        else:
#            return dha.PatMatch(node.target, dha.Name(node.id))
#    
#    def visit_SetUpdate(self, node):
#        self.generic_visit(node)
#        
#        ssym = node.target
#        if ismember(ssym):
#            cont, elem = matchpair(dka.copy(node.value))
#            newnode = dha.SetUpdate(cont.id, dka.copy(node.op), elem)
#            ### Keep old node for now to induce auxmap updates.
#            ### Should make another pass to remove it when redundant.
#            return [newnode, node]
#    
##    def visit_SetComp(self, node):
##        # Set the object-domain flag.
##        node.compinfo = dha.SC_NOT_INCR_ABLE
##        self.generic_visit(node)
#    
#    def visit_Enum(self, node):
#        self.generic_visit(node)
#        
#        ssym = node.iter
#        if not ismember(ssym):
#            return
#        
#        if isforward(node.target) or isbound(node.target):
#            cont, elem = matchpair(node.target)
#            et = dha.Enum if dha.isPosEnum(node) else dha.NegEnum
#            return et(elem, cont.id)
#    
#    visit_NegEnum = visit_Enum

### TODO: move to du
def eliminateUnused(tree):
    syms = du.UseFinder().run(tree)
    unneeded = lambda sym: ismeta(sym) or pat.isauxmap(sym) and sym not in syms
    du.EliminateUnused().run(tree, unneeded)

def leavePairDomain(tree):
    MemberPDLeaver().run(tree)
    FieldPDLeaver().run(tree)
#    eliminateUnused(tree)
