
# --- Query rewriting tools. ---

import collections
import itertools

import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du



class CompError(common.ProgramError):
    """Error in structure of comprehension."""
    pass

class CompSymbol(dha.InvSymbol):
    def refresh(self):
        self.info = RelCompInfo(self)

class RelCompInfo:
    """This structure holds auxiliary information about comprehensions
    that is useful during incrementalization, such as what variables are
    parameters and locals, and what iterated set (if any) is a U-set."""
    
    def __init__(self, compsym):
        self.compsym = compsym
        
        ordset = common.OrderedSet
        
        self.enumvars = ordset()
        self.enumlocals = ordset()
        self.enumparams = ordset()
        self.setparams = ordset()
        
        compnode = compsym.defnode.value
        
        posvars = set()
        negvars = set()
        
        # Check for bad patterns in enumerators.
        kinds = itertools.chain(*dka.findNodeTypes(compnode.enums))
        if dha.PatExpr in kinds or dha.PatIgnore in kinds:
            raise CompError('Invalid enumerator pattern')
        
        # Gather enumeration variables and iterated sets.
        for enum in compnode.enums:
            self.setparams.add(enum.iter)
            
            syms = st.gatherSymbols(enum.target)
            self.enumvars.update(syms)
            
            if dha.isPosEnum(enum):
                posvars.update(syms)
            else:
                negvars.update(syms)
        
        # Check that iterated sets are not enumeration variables.
        if set(self.setparams) & set(self.enumvars):
            raise CompError('Set parameters may not be enumeration variables')
        
        # Check safeness.
        if not negvars.issubset(posvars):
            raise CompError('Unsafe negation')
        
        # Check that result and condition expressions use only
        # enumeration variables.
        rescondvars = set()
        rescondvars.update(st.gatherSymbols(compnode.elt))
        rescondvars.update(itertools.chain(
            *(st.gatherSymbols(cond) for cond in compnode.conds)))
        
        if not rescondvars.issubset(self.enumvars):
            raise CompError('Invalid dependency on non-enum vars '
                            'in result or condition expression')
        
        # Separate locals from parameter enumvars.
        compscope = st.getNodeScope(compnode)
        for var in self.enumvars:
            if (compscope.immediateLookupSymbol(var.name, st.KIND_VSYM)
                is not None):
                self.enumlocals.add(var)
            else:
                self.enumparams.add(var)
        
        # Debug.
#        print('enumvars: ' + ', '.join(str(s) for s in self.enumvars))
#        print('enumlocals: ' + ', '.join(str(s) for s in self.enumlocals))
#        print('enumparams: ' + ', '.join(str(s) for s in self.enumparams))
#        print('setparams: ' + ', '.join(str(s) for s in self.setparams))



class ParamRewriter(dka.NodeTransformer):
    
    def visit_Name(self, node):
        if node.id.hasflag(dha.FLAG_INV):
            assert()
    
    def visit_PatMatchName(self, node):
        self.generic_visit(node)
        
        id = node.iter
        info = id.info
        params = info.enumparams
        
        if len(params) > 0:
            paramtup = du.genDPatTuple([dha.genBoundVar(sym) for sym in params])
            newtarget = dha.PatTuple([paramtup, dka.copy(node.target)])
            node.target = newtarget
        else:
            pass
    
    def visit_RelEnum(self, node):
        self.generic_visit(node)
        
        id = node.iter
        if not id.hasflag(dha.FLAG_INV):
            return
        
        info = id.info
        params = info.enumparams
        
        if len(params) > 0:
            paramtup = du.genDPatTuple([dha.genBoundVar(sym) for sym in params])
            newtarget = dha.PatTuple([paramtup, dka.copy(node.target)])
            node.target = newtarget
        else:
            pass
    
    visit_RelNegEnum = visit_RelEnum
    
    def visit_InvDef(self, node):
        dka.assertnodetype(node.value, dha.RelSetComp)
        
        self.generic_visit(node)
        
        compnode = node.value
        info = node.id.info
        params = info.enumparams
        repldict = {sym: dha.VSymbol(sym.name + '_local')
                    for sym in params}
        
        if len(params) > 0:
            paramtup = du.genDTuple([dha.Name(sym) for sym in params])
            newelt = dha.Tuple([paramtup, dka.copy(compnode.elt)])
            compnode.elt = newelt
        else:
            pass
        
        st.cleanPatterns(compnode)
        st.replaceSymbols(compnode, repldict)

def rewriteParams(tree):
    ParamRewriter().run(tree)
    du.rebuildTree(tree)



# --- Wildcard rewriting. ---

wildcard_uid = common.UID()

def hasWildcards(pattern):
    """Return whether a pattern contains any wildcards."""
    dka.assertnodetype(pattern, dha.pattern)
    if dka.hasnodetype(pattern, dha.PatIgnore):
        return True
    elif dka.hasnodetype(pattern, dha.PatTuple):
        return any(hasWildcards(e) for e in pattern.elts)
    else:
        return False

class WildcardFiller(dka.NodeTransformer):
    """Modify a pattern to replace wildcards with fresh variables."""
    def visit_PatIgnore(self, node):
        return dha.genUnboundVar(st.getFreshNSymbol())

class WildcardRewriter(dha.StmtTransformer):
    
    def helper(self, target, id):
        syms = st.gatherSymbols(target)
        
        newtarget = du.genDPatTuple([dha.PatVar(s, dha.P_UNKNOWN) for s in syms])
        
        # Generate wildcard comprehension.
        elt = du.genDTuple([dha.Name(s) for s in syms])
        enumtarget = dka.copy(target)
        st.cleanPatterns(enumtarget)
        WildcardFiller().run(enumtarget)
        enum = dha.RelEnum(enumtarget, id)
        comp = dha.RelSetComp(elt, [enum], [], dka.Symtab())
        
        num = next(wildcard_uid)
        
        repldict = {s: dha.VSymbol(s.name + '_W' + num)
                    for s in syms}
        st.replaceSymbols(comp, repldict)
        
        newid = dha.VSymbol(id.name + '_W' + num)
        
        invdef = dha.InvDef(newid, comp)
        
        ### Need a more robust way to do this part.
        oldccb = self.code_callback
        newccb = \
            (lambda ccb: oldccb(ccb) + [invdef]
                if ccb is self.CCB_NORMAL or
                   ccb is self.CCB_LOOP_ENTRY
                else [])
        
        return newtarget, newid, newccb
    
    def visit_PatMatchName(self, node):
        self.generic_visit(node)
        
        if not hasWildcards(node.target):
            return
        
        newtarget, newiter, newccb = self.helper(node.target, node.iter)
        
        node.target = newtarget
        node.iter = newiter
        self.code_callback = newccb
    
    def visit_RelEnum(self, node):
        self.generic_visit(node)
        
        if not hasWildcards(node.target):
            return
        
        newtarget, newiter, newccb = self.helper(node.target, node.iter)
        
        node.target = newtarget
        node.iter = newiter
        self.code_callback = newccb
    
    visit_RelNegEnum = visit_RelEnum

def rewriteWildcards(tree):
    WildcardRewriter().run(tree)
    du.rebuildTree(tree)

## Ehhh...
#class WildcardRewriter(dha.StmtTransformer):
#    def visit_PatMatchName(self, node):
#        if hasWildcards(node.target):
#            ###
#            assert()
#            
#            syms = st.gatherSymbols(node.target)
#            tup = du.genDPatTuple([dha.PatVar(s, dha.P_UNKNOWN) for s in syms])
#            
#            fill = WildcardFiller().run(dka.copy(node.target))
#            
#            comp = dha.SetComp(dha.patternToValue(dka.copy(tup)), [dha.Enum(fill, node.id)],
#                               None, dka.Symtab())
#            locals = st.gatherUnboundPatSyms(fill)
#            st.replaceSymbols(comp, {lv: dha.VSymbol(lv.name + '_w')
#                                     for lv in locals})
#            
#            return dha.PatMatch(tup, comp)
#    
#    def run(self, node):
#        self.compsyms = []
#        
#        super().run(node)
#        
#        return self.compsyms
#    
#    def visit_Program(self, node):
#        self.ssyms = []
#        
#        self.generic_visit(node)
#        
#        node.decls[:0] = du.genVDeclList(self.ssyms)
#        
#        print(dha.genSyntax(node))
#        
#        for ssym in self.ssyms:
#            ssym.info.updateCompInfo()
#    
#    def visit_SetCompDef(self, node):
#        self.compsyms.append(node.id)
#        self.generic_visit(node)
#    
#    def visit_Enum(self, node):
#        if hasWildcards(node.target):
#            syms = st.gatherSymbols(node.target)
#            tup = du.genDPatTuple([dha.PatVar(s, dha.P_UNKNOWN) for s in syms])
#            
#            fill = WildcardFiller().run(dka.copy(node.target))
#            
#            comp = dha.SetComp(dha.patternToValue(dka.copy(tup)), [dha.Enum(fill, node.iter)],
#                               None, dka.Symtab())
#            
#            locals = st.gatherUnboundPatSyms(fill)
#            st.replaceSymbols(comp, {lv: dha.VSymbol(lv.name + '_w')
#                                     for lv in locals})
#            
#            ssym = CompSym('W_' + next(st.freshsetvar_uid), loc = None, td = True, hasuset = False)
#            compdef = dha.SetCompDef(ssym, comp)
#            ssym.compdefs = {compdef}
#            self.ssyms.append(ssym)
#            self.compsyms.append(ssym)
#            
#            oldcallback = self.code_callback
#            self.code_callback = lambda ccb: oldcallback(ccb) + [compdef]
#            
#            return dha.Enum(tup, ssym)
#
#class WildcardReplacer(dka.NodeTransformer):
#    def run(self, node, keeps):
#        self.keeps = keeps
#        super().run(node)
#    
#    def generic_visit(self, node):
#        assert()
#    
#    def visit_PatTuple(self, node):
#        super().generic_visit(node)
#    
#    def visit_PatVar(self, node):
#        if node.id in self.keeps:
#            return
#        else:
#            return dha.PatIgnore()



#class CompError(common.ProgramError):
#    """Error in structure of comprehension."""
#    pass
#
## Counter for comprehensions.
#comp_uid = common.UID(1, 1)
#
## Named tuple type for a comprehension's location information.
#CompLoc = collections.namedtuple('CompLoc', 'func num')
#
#class CompSym(dha.InvSymbol):
#    def __init__(self, name = None, *, loc, td, hasuset):
#        self.id = next(comp_uid)
#        if name == None:
#            name = 'Comp_' + self.id
#        super().__init__(name, fixset = True)
#        
#        self.noiter = False
##        self.namedcomp = True
#        
#        self.loc = loc
#        self.compdefs = set()
#        self.info = CompInfo(self, td, hasuset)
#    
#    def getCompNode(self):
#        return next(iter(self.compdefs)).comp
#
#class CompInfo:
#    """This structure holds additional information useful for incrementalization,
#    such as the comprehension's parameters and local variables."""
#    def __init__(self, compsym, td, hasuset):
#        self.compsym = compsym
#        
#        self.td = td
#        
#        self.enumvars_od = ...
#        self.unconsparams_od = ...
#        self.consparams_od = ...
#        
#        self.uset = ... if common.dks.USET and hasuset else None
#        self.setparams = ...
#        self.enumvars = ...
#        self.localvars = ...
#        self.unconsparams = ...
#        self.consparams = ...
#        self.resultvars = ...
#        self.condvars = ...
#    
#    def updateCompInfo(self):
#        compnode = self.compsym.getCompNode()
#        
#        # Make sure that no complex terms are used in any enumerator pattern.
#        kinds = itertools.chain(*dka.findNodeTypes(compnode.enums))
#        if dha.PatExpr in kinds or dha.PatIgnore in kinds:
#            raise CompError('Invalid enumerator pattern')
#        
#        if self.uset is ...:
#            self.uset = USymbol(self.compsym)
#        
#        # We store the various symbol sets as lists to preserve the order in which they appear.
#        # This way, the emitted incrementalized code is less confusing for the user.
#        
#        ### different for od and td
#        # The variables that are defined in this scope are local.
#        self.localvars = [v for v in st.gatherSymbols(compnode)
#                            if st.getNodeScope(compnode).
#                               immediateLookupSymbol(v.name, st.KIND_VSYM) is not None]
#        
#        # Several attributes only apply to the tuple-domain comprehension.
#        if self.td:
#            
#            # The set parameters are the sets iterated over by the enumerators.
##            if self.setparams is ...:
#            self.setparams = []
#            for enum in compnode.enums:
#                sym = enum.iter
#                if sym not in self.setparams:
#                    self.setparams.append(sym)
#            
#            # The enumeration variables are the symbols that appear in the enumerator patterns.
##            if self.enumvars is ...:
#            self.enumvars = []
#            for enum in compnode.enums:
#                syms = st.gatherSymbols(enum.target)
#                for sym in syms:
#                    if sym not in self.enumvars:
#                        # Positive enumerators can introduce enumeration variables.
#                        if dha.isPosEnum(enum):
#                            self.enumvars.append(sym)
#                        # For safeness, negative enumerators must be fully-bound.
#                        else:
#                            raise CompError('Unsafe negative enumerator')
#            
#            # The ones that are in the U-set's enumerator are unconstrained parameters.
#            if self.uset is not None:
#                for enum in compnode.enums:
#                    if enum.iter is self.uset:
#                        self.unconsparams = st.gatherSymbols(enum.target)
#                        break
#                else: assert()
#            else:
#                self.unconsparams = []
#            
#            # The rest are constrained parameters.
#            self.consparams = [ev for ev in self.enumvars
#                                  if ev not in self.localvars
#                                  if ev not in self.unconsparams]
#            
#            # The result variables are variables used in the result expression.
#            # Likewise for the condition variables.
#            # TODO: This should actually allow the use of constant functions (which are
#            # symbols but not variables), but we don't even have a way of distinguishing
#            # constantness yet so we won't sweat it.
##            if self.resultvars is ... or self.condvars is ...:
#            self.resultvars = st.gatherSymbols(compnode.elt)
#            self.condvars = st.gatherSymbols(compnode.cond) if compnode.cond else []
#            restrictedvars = set(self.resultvars) | set(self.condvars)
#            if not restrictedvars.issubset(self.enumvars):
#                raise CompError('Condition and result expressions must only use '
#                                'enumeration variables.')
#        
#        else:
##            if self.enumvars_od is ...:
#                self.enumvars_od = []
#                for enum in compnode.enums:
#                    syms = st.gatherSymbols(enum.target)
#                    for sym in syms:
#                        if sym not in self.enumvars_od:
#                            self.enumvars_od.append(sym)
#            
##            if self.consparams_od is ...:
#                self.consparams_od = [ev for ev in self.enumvars_od if ev not in self.localvars]
##            if self.unconsparams_od is ...:
#                itersyms = []
#                for enum in compnode.enums:
#                    itersyms.extend(sym for sym in st.gatherSymbols(enum.iter)
#                                        if sym not in itersyms)
#                self.unconsparams_od = [sym for sym in itersyms
#                                            if sym not in self.consparams_od
#                                            if sym not in self.localvars
#                                            if not sym.fixset]
#        
##        def valid(o):
##            return o is not ... and o is not None
##        print('---')
##        print('comp: ' + dha.genSyntax(compnode))
##        if valid(self.enumvars):
##            print('enumvars: ' + ', '.join(sym.name for sym in self.enumvars))
##        if valid(self.localvars):
##            print('locals: ' + ', '.join(sym.name for sym in self.localvars))
##        if valid(self.consparams):
##            print('cons: ' + ', '.join(sym.name for sym in self.consparams))
##        if valid(self.unconsparams):
##            print('uncons: ' + ', '.join(sym.name for sym in self.unconsparams))
##        if valid(self.setparams):
##            print('setparams: ' + (', '.join(sym.name for sym in self.setparams)
##                                   if self.setparams is not None else str(None)))
##        print('---')
#
#class USymbol(dha.VSymbol):
#    def __init__(self, compsym):
#        super().__init__('U_' + compsym.id, fixset = True)
#        self.compsym = compsym
#        self.usym = True
#
#
#
##### FIXME: need to be careful about code_callback when
##### multiple setcomps are on the same statement.
##
##class ComprehensionLifter(dha.StmtTransformer):
##    
##    def run(self, node):
##        self.compsyms = []
##        self.tree = node
##        
##        super().run(node)
##        
##        # Update compinfo.
##        for s in self.compsyms:
##            s.info.updateCompInfo()
##        
##        return self.compsyms
##    
##    def visit_Program(self, node):
##        self.cls = None
##        self.func = None
##        self.compnum_stack = [1]
##        
##        self.generic_visit(node)
##        
##        # Add declarations for introduced sets.
##        node.decls[:0] = du.genVDeclList(self.compsyms)
##    
##    def visit_FunctionDef(self, node):
##        self.func = node
##        self.compnum_stack.append(1)
##        
##        self.generic_visit(node)
##        
##        self.func = None
##        self.compnum_stack.pop()
##    
##    def visit_Assign(self, node):
##        # Hackish special case for binds.
##        if dka.hasnodetype(node.value, dha.SetComp):
##            dka.assertnodetype(node.target, dha.PatVar)
##            self.visit(node.value)
##            st.replaceSymbols(self.tree, {node.target.id : self.lastcs})
##            return []
##    
##    def visit_SetComp(self, node):
##        self.generic_visit(node)
##        
##        i = self.compnum_stack[-1]
##        self.compnum_stack[-1] += 1
##        s = CompSym(loc = CompLoc(self.cls, self.func, i),
##                    td = False, hasuset = True)
##        self.lastcs = s
##        self.compsyms.append(s)
##        
##        def callback(ccb):
##            copycomp = dka.copy(node)
##            compdef = dha.SetCompDef(s, copycomp)
##            s.compdefs.add(compdef)
##            return [compdef]
##        
##        self.code_callback = callback
##        
##        return dha.Name(s)
##
##def liftComprehensions(tree):
##    return ComprehensionLifter().run(tree)
#
##class USetRewriter(dha.StmtTransformer):
##    
##    def run(self, node, comps):
##        self.comps = comps
##        
##        self.usetsyms = []
##        
##        super().run(node)
##    
##    def visit_Program(self, node):
##        self.generic_visit(node)
##        
##        node.decls[:0] = du.genVDeclList(self.usetsyms)
##    
##    def visit_SetCompDef(self, node):
##        self.generic_visit(node)
##        
##        compsym = node.id
##        if compsym not in self.comps:
##            return
##        
##        info = compsym.info
##        if info.uset is None:
##            return
##        uset = info.uset
##        
##        compnode = node.comp
##        uncons = info.unconsparams_od
##        
##        if len(uncons) == 0:
##            info.uset = None
##            return
##        
##        self.usetsyms.append(uset)
##        
##        tup = du.genDPatTuple([dha.genBoundVar(sym) for sym in uncons])
##        enum = dha.AttrEnum(tup, dha.SelName(uset))
##        compnode.enums.insert(0, enum)
##        
##        info.updateCompInfo()
##        
##        
##        uptup = dha.patternToValue(dka.copy(tup))
##        update = [dha.SetUpdate(uset, dha.UpAdd(), uptup)]
##        test = dha.UnaryOp(dha.Not(),
##                           dha.Match(dha.PatMatch(dka.copy(tup), dha.Name(uset)),
##                                     dka.Symtab()))
##        code = [dha.If([dha.CondCase(test, dha.Block(update))])]
##        self.addCode(code)
##
##def rewriteUSets(tree, comps):
##    dka.assertnodetype(tree, dha.Program)
##    return USetRewriter().run(tree, comps)
#
#class ParamRewriter(dka.NodeTransformer):
#    
#    def run(self, node, comp):
#        self.comps = {comp}
#        
#        super().run(node)
#    
#    def visit_PatMatch(self, node):
#        self.generic_visit(node)
#        
#        if not dka.hasnodetype(node.iter, dha.Name):
#            return
#        id = node.iter.id
#        
#        if id not in self.comps:
#            return
#        
#        info = id.info
#        
#        if info.uset is not None:
#            assert(len(info.unconsparams_od) == 0)
#            params = info.consparams_od
#        else:
#            params = info.unconsparams_od + info.consparams_od
#        if len(params) == 0:
#            return
#        
#        paramtup = du.genDPatTuple([dha.genBoundVar(sym) for sym in params])
#        node.target = dha.PatTuple([paramtup, dka.copy(node.target)])
#    
#    def visit_AttrEnum(self, node):
#        self.generic_visit(node)
#        
#        if not dka.hasnodetype(node.iter, dha.SelName):
#            return
#        id = node.iter.id
#        
#        if id not in self.comps:
#            return
#        
#        info = id.info
#        
#        if info.uset is not None:
#            assert(len(info.unconsparams_od) == 0)
#            params = info.consparams_od
#        else:
#            params = info.unconsparams_od + info.consparams_od
#        if len(params) == 0:
#            return
#        
#        paramtup = du.genDPatTuple([dha.genBoundVar(sym) for sym in params])
#        node.target = dha.PatTuple([paramtup, dka.copy(node.target)])
#    
#    def visit_NegEnum(self, node):
#        assert()
#    
#    def visit_SetCompDef(self, node):
#        self.generic_visit(node)
#        
#        compsym = node.id
#        if compsym not in self.comps:
#            return
#        
#        info = compsym.info
#        compnode = node.comp
#        
#        if info.uset is not None:
#            assert(len(info.unconsparams_od) == 0)
#            params = info.consparams_od
#        else:
#            params = info.unconsparams_od + info.consparams_od
#        
#        if len(params) == 0:
#            return
#        
#        paramtup = du.genDTuple([dha.Name(sym) for sym in params])
#        compnode.elt = dha.Tuple([paramtup, dka.copy(compnode.elt)])
#        
#        if info.uset:
#            replparams = params
#        else:
#            replparams = info.consparams_od
#        repldict = {p: dha.VSymbol(p.name + '_lc') for p in replparams}
#        st.replaceSymbols(compnode, repldict)
#        
#        st.cleanPatterns(compnode)
#
#def rewriteParams(tree, comps):
#    dka.assertnodetype(tree, dha.Program)
#    
#    for comp in comps:
#        ParamRewriter().run(tree, comp)
#        
#        du.rebuildTree(tree)
#        
#        for comp2 in comps:
#            info = comp2.info
#            info.updateCompInfo()
#    
##    for comp2 in comps:
##        info = comp2.info
##        print()
##        print('--'*20)
##        print('uncons ' + ','.join(s.name for s in info.unconsparams_od))
##        print('cons ' + ','.join(s.name for s in info.consparams_od))
##        print('enums ' + ','.join(s.name for s in info.enumvars_od))
#
#class ComprehensionImplementer(dka.NodeTransformer):
#    """Implement a comprehension by replacing it with a set variable,
#    and inserting code to clear and populate this set variable just
#    before it is used."""
#    
#    def run(self, node, comps):
#        self.comps = comps
#        super().run(node)
#    
#    def clauses_helper(self, comp, setsym, suffix):
#        """Generate clauses for clearing and populating a set variable,
#        using the given suffix for the local variables."""
#        # Get the locals.
#        localvars = setsym.info.localvars
#        # Copy and clean the enumerators.
#        enums = [st.cleanPatterns(dka.copy(e)) for e in comp.enums]
#        cond = dka.copy(comp.cond) if comp.cond else None
#        
#        # Add to the set at the innermost loop body.
#        update = [dha.SetUpdate(setsym, dha.UpAdd(), dka.copy(comp.elt))]
#        # Guard it for strictness.
#        match = dha.Match(dha.PatMatch(dha.PatExpr(dka.copy(comp.elt)), dha.Name(setsym)),
#                          dka.Symtab())
#        guard = [dha.If([dha.CondCase(dha.UnaryOp(dha.Not(), match), dha.Block(update))])]
#        # Construct the nested clauses.
#        clauses = du.enumsToClauses(enums, cond, guard)
##        clauses = du.enumsToClauses_reordered(enums, cond, guard, comp.scope.parentscope)
#        # Clear the set at the top.
#        clear = du.genClearCode(False, setsym)
#        
#        code = clear + clauses
#        # Rename local variables to ensure uniqueness.
#        instmap = {lv: dha.VSymbol(lv.name + suffix)
#                   for lv in localvars}
#        st.replaceSymbols(code, instmap)
#        
#        return code
#    
#    def visit_SetCompDef(self, node):
#        id = node.id
#        if id not in self.comps:
#            return
#        comp = node.comp
#        
#        uid = next(st.freshvar_uid)
##        suffix = '_S' + node.id.uid
#        suffix = '_v' + uid
#        
#        code = self.clauses_helper(comp, id, suffix)
#        
#        return code
#
#def implementComprehensions(code, compnodes):
#    ComprehensionImplementer().run(code, compnodes)
#
