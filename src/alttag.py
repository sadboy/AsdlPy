
import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du
import computils as cu
import pair

class TagSym(cu.CompSym):
    def __init__(self, name):
        super().__init__(name, loc = None, td = True, hasuset = False)
        self.tagsym = True

class TagInfo():
    pass

def genTagInfo(comp):
    info = comp.info
    compnode = comp.getCompNode()
    
    uset = info.uset
    if uset is None:
        return
    
    enums = compnode.enums
    assert(enums[0].iter is uset)
    rootsyms = set(st.gatherSymbols(enums[0].target))
    unconsparams = info.unconsparams
    assert(rootsyms == set(unconsparams))
    
    taginfo = TagInfo()
    info.taginfo = taginfo
    taginfo.compinfo = info
    
    pairenums = enums[1:]
    
    taginfo.As = As = []
    taginfo.Bs = Bs = []
    taginfo.Rs = Rs = []
    taginfo.DRs = DRs = []
    
    for i, enum in enumerate(pairenums):
        dka.assertnodetype(enum.target, dha.PatTuple)
        elts = enum.target.elts
        assert(len(elts) == 2)
        dka.assertnodetype(elts[0], dha.PatVar)
        dka.assertnodetype(elts[1], dha.PatVar)
        
        cont, elem = elts[0].id, elts[1].id
        rel = enum.iter
        
        As.append(cont)
        Bs.append(elem)
        Rs.append(rel)
        
        demrel = TagSym('Dm_' + info.compsym.id + '_' + str(i+1))
        DRs.append(demrel)
    
    taginfo.tagcomps = tagcomps = []
    
    # Generate auxiliary demand comprehensions.
    for i, (a, b, r, dr) in enumerate(zip(As, Bs, Rs, DRs)):
        tagenums = []
        
        # Add U pred.
        if a in unconsparams:
            k = unconsparams.index(a)
            ig1 = [dha.PatIgnore() for z in range(0, i)]
            ig2 = [dha.PatIgnore() for z in range(i+1, len(unconsparams))]
            tup = du.genDPatTuple(ig1 + [dha.genUnboundVar(a)] + ig2)
            e = dha.Enum(tup, uset)
            tagenums.append(e)
        
        # Add other preds.
        for a2, b2, r2, dr2 in list(zip(As, Bs, Rs, DRs))[:i]:
            if b2 is a:
                tup = dha.PatTuple([dha.PatIgnore(), dha.genUnboundVar(b2)])
                e = dha.Enum(tup, dr2)
                tagenums.append(e)
        
        # Add orig relation.
        assert(len(tagenums) > 0)
        tup = dha.PatTuple([dha.genUnboundVar(a), dha.genUnboundVar(b)])
        e = dha.Enum(tup, r)
        tagenums.append(e)
        
        comp = dha.SetComp(dha.Tuple([dha.Name(a), dha.Name(b)]), tagenums,
                           None, dka.Symtab())
        
        instmapping = {s: dha.VSymbol(s.name + '_t' + str(i))
                       for s in set(As) | set(Bs)}
        st.replaceSymbols(comp, instmapping)
        
        compdef = dha.SetCompDef(dr, comp)
        tagcomps.append(compdef)
    
    return taginfo

class TagCompInserter(dka.NodeTransformer):
    
    def run(self, node, comp):
        self.comp = comp
        
        self.tagcompsyms = []
        
        super().run(node)
        
        for s in self.tagcompsyms:
            s.info.updateCompInfo()
    
    def visit_Program(self, node):
        self.generic_visit(node)
        
        node.decls[:0] = du.genVDeclList(self.tagcompsyms)
    
    def visit_SetCompDef(self, node):
        if node.id is not self.comp:
            return
        
        taginfo = self.comp.info.taginfo
        
        code = []
        
        for tc in taginfo.tagcomps:
            newtc = dka.copy(tc)
            code.append(newtc)
            sym = tc.id
            sym.compdefs.add(newtc)
            self.tagcompsyms.append(sym)
        
        code.append(dka.copy(node))
        
        return code

class TagConstraintInserter(dka.NodeTransformer):
    
    def run(self, node, comp):
        self.comp = comp
        
        super().run(node)
    
    def visit_SetCompDef(self, node):
        self.generic_visit(node)
        
        compsym = node.id
        if compsym is not self.comp:
            return
        
        info = compsym.info
        taginfo = info.taginfo
        
        compnode = node.comp
        
        for enum, r, dr in zip(compnode.enums[1:], taginfo.Rs, taginfo.DRs):
            assert(enum.iter is r)
            enum.iter = dr
        
        ### ug
        assert(len(compsym.compdefs) == 1)
        compsym.compdefs = {node}
        
        info.updateCompInfo()

def tagify(tree, comp):
    genTagInfo(comp)
    TagCompInserter().run(tree, comp)
    TagConstraintInserter().run(tree, comp)
