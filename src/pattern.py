################################################################################
# pattern.py: Pattern matching implementation.                                 #
# Author: Jon Brandvein                                                        #
################################################################################

### TODO: describe mask, bounds/unbounds tuples



import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du



class PatternError(common.ProcessError):
    pass

class AuxMapSymbol(dha.VSymbol):
    """Symbol for a bound-unbound map. Host is the set symbol that this
    map serves as an index for. Mask is string representing the pattern's
    structure. Pat is a copy of the actual pattern tree."""
    def __init__(self, host, mask, pat):
        ### FIXME: fixset flag is hackish at the moment.
        self.host = host
        self.mask = mask
        self.pat = pat
        super().__init__(host.name + '_' + mask, fixset = True, kind = 'multidict')

def isauxmap(sym):
    """Test whether a symbol is an AuxMapSymbol."""
    assert(isinstance(sym, dka.Symbol))
    return isinstance(sym, AuxMapSymbol)

def maskAllBound(mask):
    """Test whether a mask represents a fully-bound pattern."""
    return all(c in {'b', 'l', 'r'} for c in mask)

def maskAllUnbound(mask):
    """Test whether a mask represents a fully-unbound pattern."""
    return all(c in {'u', 'l', 'r'} for c in mask)

def nameFromMask(mask):
    # If the mask is for a tuple of length more than 1,
    # the tuple-delimiting characters are redundant.
    # TODO: Better way of determining whether any two auxmaps are ambiguous
    # and avoiding the characters.
    if len(mask) >= 4:
        assert(mask.startswith('l') and mask.endswith('r'))
        mask = mask[1:-1]

class PatternMasker(dka.NodeVisitor):
    """Given a pattern, return its mask, as well as its
    bounds and unbounds tuples."""
    
    def run(self, node):
        self.bounds = []
        self.unbounds = []
        
        mask = super().run(node)
        
        bounds = du.genDTuple(self.bounds)
        
        unbounds = du.genDPatTuple(self.unbounds)
        
        return mask, bounds, unbounds
    
    def generic_visit(self, node):
        assert()
    
    def visit_PatTuple(self, node):
        return 'l' + ''.join(self.visit(elt) for elt in node.elts) + 'r'
    
    def visit_PatVar(self, node):
        if dha.isBoundPatVar(node):
            self.bounds.append(dha.Name(node.id))
            return 'b'
        
        else:
            self.unbounds.append(dha.genUnboundVar(node.id))
            return 'u'
    
    def visit_PatExpr(self, node):
        self.bounds.append(node.value)
        return 'b'

class PatternGenericizer(dka.NodeVisitor):
    """Given a pattern, return its generic tuple tree,
    and bounds and unbounds tuples of the tree."""
    
    def run(self, node):
        self.bounds = []
        self.unbounds = []
        
        generictree = super().run(node)
        
        bounds = du.genDTuple(self.bounds)
        
        unbounds = du.genDTuple(self.unbounds)
        
        return generictree, bounds, unbounds
    
    def generic_visit(self, node):
        assert()
    
    def visit_PatTuple(self, node):
        return dha.PatTuple([self.visit(elt) for elt in node.elts])
    
    def visit_PatVar(self, node):
        v = st.getFreshNSymbol()
        
        if dha.isBoundPatVar(node):
            self.bounds.append(dha.Name(v))
            return dha.genUnboundVar(v)
        
        else:
            self.unbounds.append(dha.Name(v))
            return dha.genUnboundVar(v)
    
    def visit_PatExpr(self, node):
        v = st.getFreshNSymbol()
        self.bounds.append(dha.Name(v))
        return dha.genUnboundVar(v)

def getPatInfo(pattree):
    return PatternMasker().run(pattree)

def getPatMask(pattree):
    mask, _, _ = PatternMasker().run(pattree)
    return mask

def getDecomposition(pattree):
    return PatternGenericizer().run(pattree)



class Depatternizer(dka.NodeTransformer):
    
    def getAuxSym(self, ssym, mask, pat):
        """Retrieve the auxiliary map symbol for the given set symbol and mask."""
        if (ssym, mask) in self.auxmaskmap:
            auxsym = self.auxmaskmap[(ssym, mask)]
            return auxsym
        else:
            auxsym = AuxMapSymbol(ssym, mask, dka.copy(pat))
            self.auxmaskmap[(ssym, mask)] = auxsym
            return auxsym
    
    def run(self, node):
        self.auxmaskmap = {}
        super().run(node)
        return self.auxmaskmap
    
    def patmatch_helper(self, patmatch):
        target = patmatch.target
        
        if dka.hasnodetype(patmatch, dha.PatMatchName):
            iter = dha.Name(patmatch.id)
        
        elif dka.hasnodetype(patmatch, dha.PatMatchLookup):
            iter = dha.Lookup(patmatch.id, dka.copy(patmatch.key))
        
        else: assert()
        
        return target, iter
    
    def visit_Program(self, node):
        self.generic_visit(node)
        
        # Insert declarations for the auxiliary maps.
        node.decls[:0] = du.genVDeclList(self.auxmaskmap.values())
    
    def visit_Assign(self, node):
        # Make sure the LHS is all unbound.
        ### TODO: Clarify position on bound variables in assignments.
        mask = getPatMask(node.target)
        assert(maskAllUnbound(mask))
        self.generic_visit(node)
    
    def visit_PatMatchName(self, node):
        # Descend to make sure we get nested PatMatch nodes
        # (i.e., inside PatExpr nodes).
        
        self.generic_visit(node)
        
        mask, bounds, unbounds = getPatInfo(node.target)
        
        # If fully bound or unbound, let the parent worry
        # about further transformation.
        if maskAllBound(mask) or maskAllUnbound(mask):
            return node 
        
        # Otherwise, replace with a map lookup.
        else:
            ssym = node.id
            auxsym = self.getAuxSym(ssym, mask, node.target)
            return dha.PatMatchLookup(unbounds, auxsym, bounds)
    
    def visit_PatCase(self, node):
        # Transform the PatMatch node first.
        self.generic_visit(node)
        
        target, iter = self.patmatch_helper(node.match)
        mask = getPatMask(target)
        
        # If fully bound, replace with a membership test.
        if maskAllBound(mask):
            test = dha.BinOp(dha.patternToValue(target), dha.In(), iter)
            code = dha.CondCase(test, node.body)
        
        # Otherwise, replace with a non-emptiness test and a binding.
        else:
            elem = dha.UnaryOp(dha.Any(), iter)
            node.body.stmtlist[:0] = [dha.Assign(target, elem)]
            emptytest = dha.UnaryOp(dha.NotEmpty(), dka.copy(iter))
            code = dha.CondCase(emptytest, node.body)
        
        return code
    
    def visit_For(self, node):
        # Transform the PatMatch node first.
        self.generic_visit(node)
        
        target, iter = self.patmatch_helper(node.match)
        mask = getPatMask(target)
        
        # If fully bound, replace with an If.
        if maskAllBound(mask):
            test = dha.BinOp(dha.patternToValue(target), dha.In(), iter)
            code = dha.If([dha.CondCase(test, node.body)],
                          node.orelse)
        
        # Otherwise, take no action. (The PatMatch has already been rewritten as a lookup.)
        else:
            code = node
        
        return code
    
    def visit_PatWhile(self, node):
        # Transform the PatMatch node first.
        self.generic_visit(node)
        
        target, iter = self.patmatch_helper(node.match)
        mask = getPatMask(target)
        
        # If fully bound, replace with a condition While.
        if maskAllBound(mask):
            test = dha.BinOp(dha.patternToValue(target), dha.In(), iter)
            code = dha.While(test, node.body, node.orelse)
        
        # Otherwise, test non-emptiness and bind.
        else:
            elem = dha.UnaryOp(dha.Any(), iter)
            node.body.stmtlist[:0] = [dha.Assign(target, elem)]
            emptytest = dha.UnaryOp(dha.NotEmpty(), dka.copy(iter))
            code = dha.While(emptytest, node.body, node.orelse)
        
        return code
    
    def visit_Match(self, node):
        self.generic_visit(node)
        
        target, iter = self.patmatch_helper(node.match)
        mask = getPatMask(target)
        
        if maskAllBound(mask):
            code = dha.BinOp(dha.patternToValue(target), dha.In(), iter)
        else:
            code = dha.UnaryOp(dha.NotEmpty(), iter)
        
        return code
    
    def visit_Pick2nd(self, node):
        self.generic_visit(node)
        
        tup = dha.PatTuple([dha.PatExpr(node.key),
                            dha.genUnboundVar(st.getFreshNSymbol())])
        mask, bounds, unbounds = getPatInfo(tup)
        
        ssym = node.id
        auxsym = self.getAuxSym(ssym, mask, tup)
        
        code = dha.UnaryOp(dha.Any(), dha.Lookup(auxsym, bounds))
        
        return code
    
#    def visit_SetComp(self, node):
#        node.compinfo = dha.SC_NOT_INCR_ABLE
#        self.generic_visit(node)
    
#    def visit_Enum(self, node):
#        self.generic_visit(node)
#        
#        mask, bounds, unbounds = getPatInfo(node.target)
#        ssym = node.iter
#        
#        if maskAllBound(mask):
#            code = dha.EnumIf(dha.patternToValue(node.target), dha.Name(ssym))
#        
#        elif maskAllUnbound(mask):
#            code = dha.EnumFor(node.target, dha.Name(ssym))
#        
#        else:
#            auxsym = self.getAuxSym(ssym, mask, node.target)
#            code = dha.EnumFor(unbounds, dha.Lookup(auxsym, bounds))
#        
#        return code
#    
#    visit_NegEnum = visit_Enum
#    
#    def visit_AttrEnum(self, node):
#        self.generic_visit(node)
#        
#        mask, bounds, unbounds = getPatInfo(node.target)
#        
#        if maskAllBound(mask):
#            code = dha.EnumIf(dha.patternToValue(node.target), dha.selectorToAttr(node.iter))
#        
#        elif maskAllUnbound(mask):
#            code = dha.EnumFor(node.target, dha.selectorToAttr(node.iter))
#        
#        else:
#            dka.assertnodetype(node.iter, dha.SelName)
#            ssym = node.iter.id
#            auxsym = self.getAuxSym(ssym, mask, node.target)
#            code = dha.EnumFor(unbounds, dha.Lookup(auxsym, bounds))
#        
#        return code
#    
#    visit_NegAttrEnum = visit_AttrEnum

class AuxMapUpdater(dka.NodeTransformer):
    
    def run(self, node, auxmaskmap):
        self.maskmap = common.setdict()
        for ((ssym, mask), auxsym) in auxmaskmap.items():
            self.maskmap[ssym].add((mask, auxsym))
        super().run(node)
    
    def visit_SetUpdate(self, node):
        ssym = node.target
        
        code = [node]
        
        for mask, auxsym in sorted(self.maskmap[ssym],
                                   key = lambda elem: elem[1].name):
            pat = auxsym.pat
            tupletree, bounds, unbounds = getDecomposition(pat)
            
            update = [dha.MapUpdate(auxsym, bounds, dka.copy(node.op), unbounds)]
            newcode = [dha.If([dha.ApplCase(tupletree, node.value,
                                            dha.Block(update))])]
            
            code.extend(newcode)
        
        return code

def depatternize(code):
    auxmaskmap = Depatternizer().runBoth(code)
    return auxmaskmap

### FIXME: Apparently sometimes a set doesn't end up in hostsyms
### because it has no entry in auxmaskmap because it has no
### aux maps, and then the original set won't be eliminated for some
### reason.
def auxmapupdates(code, auxmaskmap):
    hostsyms = {ssym for (ssym, mask) in auxmaskmap.keys()}
    auxsyms = {auxsym for auxsym in auxmaskmap.values()}
    usedsyms = du.UseFinder().run(code)
    
    usedaux = auxsyms & usedsyms
    
    auxmaskmap = {(ssym, mask): auxsym
                  for (ssym, mask), auxsym in auxmaskmap.items()
                  if auxsym in usedaux}
    
    AuxMapUpdater().runBoth(code, auxmaskmap)
    
    unusedsyms = (hostsyms | auxsyms) - usedsyms
    
    du.EliminateUnused().run(code, lambda sym: sym in unusedsyms)
