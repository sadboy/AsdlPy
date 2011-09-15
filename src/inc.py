################################################################################
# inc.py: Incrementalize a comprehension.                                      #
# Author: Jon Brandvein                                                        #
################################################################################

import itertools
import collections

import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du
import computils as cu



class CompIncInfo:
    
    def __init__(self, compsym):
        self.compsym = compsym
        self.compinfo = info = compsym.info
        self.compnode = compsym.defnode.value
        
        # Generate result map.
        self.resmapsym = dha.VSymbol('Resmap_' + compsym.name,
                                     flags = {du.FLAG_REFCOUNTED})
        self.diffsym = dha.VSymbol('Diff_' + compsym.name)
    
    def genDSetBlock(self, enumnum, upvalexpr):
        compnode = self.compnode
        enumvars = self.info.enumvars
        
        enums = dka.copy(compnode.enums)
        conds = dka.copy(compnode.conds)
        st.cleanPatterns(enums)
        
        suffix = '_up' + str(enumnum)
        
        wittarget = dka.copy(enums[enumnum].target)
        upval = dka.copy(upvalexpr)
        upvalassign = dha.Assign(wittarget, upval)
        elt = du.genDTuple([s for s in enumvars])
        
        if len(enums) > 1:
            maintenums = enums[:enumnum] + enums[enumnum+1:]
            maintcomp = dha.RelSetComp(elt, maintenums, conds, dka.Symtab())
            maintupdate = dha.SetUpdate(self.diffsym, dha.UpUnionNS(), maintcomp)
        else:
            maintupdate = dha.SetUpdate(self.diffsym, dha.UpAddNS(), elt)
        
        code = [upvalassign, maintupdate]
        
        repldict = {s: dha.VSymbol(s.name + suffix)
                    for s in enumvars}
        st.replaceSymbols(code, repldict)
        
        return code
    
    def genHandler(self, setparam, isaddition):
        compnode = self.compnode
        
        code = []
        
        # Compute differential assignment set.
        for i, enum in enumerate(compnode.enums):
            if enum.iter is setparam:
                code.extend(self.genDSetBlock(i))
        
        # Compute change to result set.
        vartup = du.genDPatTuple([s for s in enumvars])
        match = dha.PatMatchName(vartup, self.diffsym)
        resexpr = dka.copy(compnode.elt)
#        update = dha.SetUpdate(self.resmapsym, dha.UpAddNS(), resexpr)
        update = dha.SetUpdate(self.resmapsym, dha.UpAdd(), resexpr)
        loop = dha.For(match, dha.Block([update]))
        
        code.extend([loop])







## Query incrementalization is handled by two classes. First, CompIncInfo
## produces maintenance code templates that can be instantiated for any update.
## Then, ComprehensionIncrementalizer visits the tree, adding a declaration for
## the result map, inserting instantiated maintenance code, and changing the query
## to use the result map.
#
#import itertools
#import collections
#
#import common
#import darkitast as dka
#import darhiast as dha
#import symtab as st
#import darkitutils as du
#import computils as cu
#
#class IncError(common.ProcessError):
#    """Trouble performing incrementalization."""
#    pass
#
#
#
## Count the number of comprehensions that have been incrementalized.
## (If there is only one, we can omit the comprehension uid suffix
## from the maintenance code variables.)
#numincrcomps = common.UID(0)
#
## Placeholder symbol used in the update template;
## will be expanded to the update expression when instantiated.
#update_expr_sym = dha.VSymbol('update_expr')
#
#class CodeBlockSymbol(dha.VSymbol):
#    """VSymbol for use in maintenance code."""
#    
#    def __init__(self, basename, compnum, blocknum, updatenum = None):
#        # Call super().__init__. The name will be ignored due to the property.
#        super().__init__('CBSYM')
#        
#        self.basename = basename
#        self.compnum = compnum
#        self.blocknum = blocknum
#        self.updatenum = updatenum
#    
#    @property
#    def name(self):
#        return (self.basename + '_'
#              + ('c' + self.compnum if numincrcomps.counter != 1 else '')
#              + (('u' + self.updatenum) if self.updatenum is not None else '')
#              + ('b' + self.blocknum if self.blocknum is not None else ''))
#    @name.setter
#    def name(self, value):
#        pass
#
#class CodeBlock:
#    """Class to encapsulate a maintenance code block template
#    and its extra info - its block number and whether it comes
#    before or after the update."""
#    
#    def __init__(self, codetemplate, after, witnum, witness_clause, compincinfo, blocknum):
#        self.codetemplate = codetemplate
#        self.after = after
#        self.witnum = witnum
#        self.witness_clause = witness_clause
#        self.compincinfo = compincinfo
#        self.blocknum = blocknum
#    
#    def instantiate(self, updateexpr, updatenum = None):
#        """Instantiate the template by specifying the update uid
#        and the update expression."""
#        
#        code = dka.copy(self.codetemplate)
#        
#        witness_target = dka.copy(self.witness_clause.target)
#        witness_iter = self.witness_clause.iter
#        
#        code = [dha.If([dha.ApplCase(witness_target, dha.Name(update_expr_sym),
#                                     dha.Block(code))])]
#        
#        enumvars = self.compincinfo.compinfo.enumvars
#        
#        # Replace the enumeration variables with real variables
#        # that are unique to this code block.
#        instmapping = {enumvar: CodeBlockSymbol(enumvar.name, self.compincinfo.compnum,
#                                                self.blocknum, updatenum)
#                       for enumvar in enumvars}
#        st.replaceSymbols(code, instmapping)
#        
#        # Expand the update expression placeholder with the
#        # actual update expression.
#        expmapping = {update_expr_sym: dka.copy(updateexpr)}
#        st.expandSymbols(code, expmapping)
#        
#        return code
#
#
#
#class CompIncInfo:
#    """Generate and store the information needed to incrementalize a comprehension."""
#    
#    # Comprehension counter, for numbering the result map
#    # and the maintenance code variables.
#    comp_uid = common.UID(1, 1)
#    
#    def __init__(self, comp):
#        # Store comprehension node.
#        self.comp = comp
#        self.compnode = comp.getCompNode()
#        self.compinfo = info = comp.info
#        
#        # Generate a uid for this comprehension.
#        self.compnum = next(self.comp_uid)
#        
#        # Pick a result map name.
##        if comp.noiter:
##            self.resmapsym = comp
##        else:
##            self.resmapsym = du.RCSSymbol('Resmap_' + self.compnum)
#        self.resmapsym = comp
#        self.resmapsym.needsmulti = True
#        
#        self.dsetsym = dha.VSymbol('D_' + self.compnum)
#        
#        # The result/condition variables should all be enumeration variables;
#        # no unconstrained parameters are allowed in these expressions.
#        for v in info.resultvars + info.condvars:
#            if v not in info.enumvars:
#                raise IncError('Comprehension result and condition expressions '
#                               'may only depend on enumeration variables '
#                               '(found var {})', v.name)
#        
#        # Set up update code templates.
#        self.updatetemplates = collections.defaultdict(lambda: list())
#        for setparam in self.compinfo.setparams:
#            self.generateUpdateTemplate(setparam, True)
#            self.generateUpdateTemplate(setparam, False)
#        
#        self.genHandlers()
#        
#        # Initialize counter for applying update templates.
#        self.update_uid = common.UID(1, 1)
#    
#    def generateUpdateTemplate(self, setparam, addition):
#        """Generate a maintenance code template for a particular set parameter
#        and update operation, and add it to self.updatetemplates. The argument
#        "addition" specifies the update operation: True for UpAdd, False for UpRemove."""
#        # Copy the enumerators, and clean them by setting their boundedness to unknown.
#        # Variable boundedness will be decided after the code is generated, by a
#        # run of SymtabBuilder.
#        enums = [st.cleanPatterns(dka.copy(e)) for e in self.compnode.enums]
#        # Eh..
#        enummap = {e1: e2 for e1, e2 in zip(enums, self.compnode.enums)}
#        cond = dka.copy(self.compnode.cond) if self.compnode.cond else None
#        
#        # We maintain a counter for code blocks, so that each one's variables
#        # can be tagged with a unique identifier so they don't clash.
#        block_uid = common.UID(1, 1)
#        
#        # Find all witness clauses - clauses that iterate over the updated set.
#        witclauses = [(i, e) for i, e in enumerate(enums) if e.iter == setparam]
#        
#        # For each witness clause, produce a code block and add it to the template.
#        for witnum, witness_clause in witclauses:
#            # List the clauses besides the current witness clause.
#            other_clauses = [e for e in enums if e is not witness_clause]
#            
#            # Determine whether this is a positive enumerator, and
#            # whether we should add to or remove from the result map.
#            positive = dha.isPosEnum(witness_clause)
#            resmapadd = (addition and positive) or (not addition and not positive)
#            
#            # Grab a block uid.
#            blockid = next(block_uid)
#            
#            # Produce the code block, from the inside-out.
#            
#            # Start with the result map update. The value added to or removed
#            # from the result map is a tuple of constrained parameters and
#            # the result expression. If there are no constrained parameters,
#            # the singleton tuple is eliminated.
##            keys = du.genDTuple([dha.Name(sym) for sym in self.compinfo.unconsparams + 
##                                                          self.compinfo.consparams])
##            tup = dha.Tuple([keys] + [dka.copy(self.compnode.elt)])
#            
#            tup = dha.Tuple([dha.Name(ev) for ev in self.compinfo.enumvars])
#            code = [dha.SetUpdate(self.dsetsym,
#                                  dha.UpAdd(),
#                                  tup)]
#            test = dha.Match(dha.PatMatchName(dha.valueToPattern(dka.copy(tup)),
#                                              self.dsetsym),
#                             dka.Symtab())
#            code = [dha.If([dha.CondCase(dha.UnaryOp(dha.Not(), test),
#                                         dha.Block(code))])]
#            
##            tup = dka.copy(self.compnode.elt)
##            code = [dha.SetUpdate(self.resmapsym,
##                                  dha.UpAdd() if resmapadd else dha.UpRemove(),
##                                  tup)]
#            
#            # For each enumerator besides the chosen witness clause,
#            # create a nested For loop or If statement (inside-out order).
#            if common.dks.REORDER_CLAUSES:
#                code = du.enumsToClauses_reordered(other_clauses, cond, code,
#                                                   st.gatherSymbols(witness_clause.target))
#            else:
#                code = du.enumsToClauses(other_clauses, cond, code)
#            
#            # Create the CodeBlock object with wrapper info.
#            cb = CodeBlock(code, resmapadd, witnum, dka.copy(witness_clause), self,
#                           # Omit the block identifier if there is only one block.
#                           blockid if len(witclauses) != 1 else None)
#            # Add it to the update templates.
#            self.updatetemplates[(setparam, addition)].append(cb)
#    
#    def genDRHandler(self, add):
#        up = dha.UpAdd() if add else dha.UpRemove()
#        
#        resexpr = dka.copy(self.compnode.elt)
#        code = [dha.SetUpdate(self.resmapsym, up, resexpr)]
#        tup = dha.PatTuple([dha.genUnboundVar(ev) for ev in self.compinfo.enumvars])
#        match = dha.PatMatchName(tup, self.dsetsym)
#        code = [dha.For(match, dha.Block(code))]
#        
#        remsym = st.getFreshNSymbol()
#        rem = [dha.SetUpdate(self.dsetsym, dha.UpRemove(), dha.Name(remsym))]
#        clearmatch = dha.PatMatchName(dha.genUnboundVar(remsym),
#                                      self.dsetsym)
#        code.extend([dha.PatWhile(clearmatch, dha.Block(rem))])
#        
#        instmapping = {enumvar: dha.VSymbol(enumvar.name + '_dr')
#                       for enumvar in self.compinfo.enumvars}
#        st.replaceSymbols(code, instmapping)
#        
#        return code
#    
#    def genHandlers(self):
#        self.decls = decls = []
#        self.handlers = handlers = common.setdict()
#        
#        self.dset_addhandler = dha.FSymbol('dr_' + self.compnum + '_add')
#        self.dset_removehandler = dha.FSymbol('dr_' + self.compnum + '_remove')
#        
#        addh = dha.FunctionDef(self.dset_addhandler,
#                               [],
#                               dha.Block(self.genDRHandler(True)),
#                               dka.Symtab())
#        removeh = dha.FunctionDef(self.dset_removehandler,
#                                  [],
#                                  dha.Block(self.genDRHandler(False)),
#                                  dka.Symtab())
#        self.decls.append(addh)
#        self.decls.append(removeh)
#        
#        if not common.dks.INLINE:
#            for (updatesym, op), cbs in self.updatetemplates.items():
#                for cb in cbs:
#                    fsym = dha.FSymbol('up_' + self.compnum + '_' + updatesym.name + '_'
#                                     + ('add' if op else 'remove')
#                                     + (('_b' + cb.blocknum) if cb.blocknum is not None else ''))
#                    handlers[(updatesym, op)].add((fsym, cb.after))
#                    
#                    upvalsym = st.getFreshNSymbol()
#                    
#                    code = cb.instantiate(dha.Name(upvalsym))
#                    
#                    body = dha.Block(code)
#                    
#                    func = dha.FunctionDef(fsym, [dha.Argument(upvalsym)], body, dka.Symtab())
#                    
#                    decls.append(func)
#        
#        decls.sort(key = lambda elem: elem.id.name)
#    
#    def getDecls(self):
##        if not self.comp.noiter:
##            resmapdecl = du.genVDeclList([self.resmapsym])
##        else:
##            resmapdecl = []
#        resmapdecl = []
#        dsetdecl = du.genVDeclList([self.dsetsym])
#        return dsetdecl + resmapdecl + dka.copy(self.decls)
#    
#    def applyUpdateTemplate(self, update_node):
#        """Instantiate and insert a template for a given update."""
#        updatesym = update_node.target
#        op = dha.isAddUpdate(update_node)
#        
#        # Use a new id for each update, so the variables are fresh.
#        updateid = next(self.update_uid)
#        
#        uset = self.compinfo.uset
#        
#        precode = []
#        postcode = []
#        
#        if common.dks.INLINE:
#            # Get the code template for this update set and operation.
#            cbs = self.updatetemplates[(updatesym, op)]
#            
#            for cb in cbs:
#                (postcode if cb.after else precode).extend(
#                    cb.instantiate(update_node.value, updateid))
#        else:
#            hs = self.handlers[(updatesym, op)]
#            for func, after in hs:
#                (postcode if after else precode).extend(
#                    [dha.CallProc(func, [dka.copy(update_node.value)])])
#        
#        # Resultset/dset stuff.
#        if precode != []:
#            precode.extend([
#                dha.CallProc(self.dset_removehandler, [])])
#        if postcode != []:
#            postcode.extend([
#                dha.CallProc(self.dset_addhandler, [])])
#        
#        # Return the new code.
#        code = precode + [update_node] + postcode
#        return code
#
#
#
#### hack, ack
#def sortDecls(decls):
#    vdecls = []
#    fdecls = []
#    for decl in decls:
#        if dka.hasnodetype(decl, dha.VDecl):
#            vdecls.append(decl)
#        else:
#            fdecls.append(decl)
#    decls[:] = vdecls + fdecls
#
#class ComprehensionIncrementalizer(dka.NodeTransformer):
#    """Incrementalize a comprehension. Add the result map declaration,
#    insert maintenance code, and change the query site to use the result map."""
#    
#    def run(self, node, incrcomp):
#        assert(isinstance(incrcomp, cu.CompSym))
#        
#        self.compsym = incrcomp
#        self.compincinfo = CompIncInfo(incrcomp)
#        
#        return super().run(node)
#    
#    def visit_Program(self, node):
#        node.decls[:0] = self.compincinfo.getDecls()
#        
#        sortDecls(node.decls)
#        
#        self.generic_visit(node)
#    
#    def visit_PatMatchName(self, node):
#        self.generic_visit(node)
#        
#        itersym = node.id
#        if itersym is not self.compsym:
#            return
#        
#        if not itersym.noiter:
#            return
#        return
#        
#        
#        
#        resmapsym = self.compincinfo.resmapsym
#        unconsparams = itersym.info.unconsparams
#        consparams = itersym.info.consparams
#        
#        keys = du.genDTuple([dha.Name(p) for p in unconsparams + consparams])
#        tup = dha.PatTuple([dha.PatExpr(keys),
#                            node.target])
#        
#        return dha.PatMatchName(tup, resmapsym)
#    
#    def visit_Enum(self, node):
#        self.generic_visit(node)
#        
#        itersym = node.iter
#        if itersym is not self.compsym:
#            return
#        
#        if not itsersym.noiter:
#            return
#        return
#        
#        
#        
#        resmapsym = self.compincinfo.resmapsym
#        unconsparams = itersym.info.unconsparams
#        consparams = itersym.info.consparams
#        
#        keys = du.genDTuple([dha.Name(p) for p in unconsparams + consparams])
#        tup = dha.PatTuple([dha.PatExpr(keys),
#                            node.target])
#        
#        return dha.Enum(tup, resmapsym)
#    
#    def visit_SetCompDef(self, node):
#        compsym = node.id
#        if compsym is not self.compsym:
#            return
#        
#        # Delete the SetCompDef node altogether if no copying is needed.
#        # The result map will be used directly.
##        if compsym.noiter:
##            return []
#        return []
#        
#        
#        
#        resmapsym = self.compincinfo.resmapsym
#        unconsparams = compsym.info.unconsparams
#        consparams = compsym.info.consparams
#        
#        v = st.getFreshNSymbol()
#        keys = du.genDTuple([dha.Name(p) for p in unconsparams + consparams])
#        match = dha.PatMatchName(dha.PatTuple([dha.PatExpr(keys),
#                                               dha.genUnboundVar(v)]),
#                                 resmapsym)
#        update = [dha.SetUpdate(node.id, dha.UpAdd(), dha.Name(v))]
#        code = [dha.For(match, dha.Block(update))]
#        
#        # Gen clear code; should refactor to use du.genClearCode
#        # but have issue with pair conversion.
##        code = du.genClearCode(True, node.id.mem) + code
#        v = st.getFreshNSymbol()
#        match = dha.genPatMatchSym(True,
#                                   dha.genUnboundVar(v),
#                                   node.id)
#        update = [dha.SetUpdate(node.id, dha.UpRemove(), dha.Name(v))]
#        clear = [dha.PatWhile(match, dha.Block(update))]
#        
#        code = clear + code
#        
#        return code
#    
#    def visit_SetUpdate(self, node):
#        # If this is an update to a set parameter, insert maintenance code.
#        if node.target in self.compincinfo.compinfo.setparams:
#            code = self.compincinfo.applyUpdateTemplate(node)
#            return code
#
#def incrementalizeComprehension(tree, incrcomp):
#    """Incrementalize a comprehension. Return the new tree
#    and the CompIncInfo object."""
#    compincr = ComprehensionIncrementalizer()
#    tree = compincr.run(tree, incrcomp)
#    
#    # Increment the global counter.
#    next(numincrcomps)
#    
#    return (tree, compincr.compincinfo)
