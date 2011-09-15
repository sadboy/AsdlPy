################################################################################
# symtab.py: Process symbol table information.                                 #
# Author: Jon Brandvein                                                        #
################################################################################

### TODO: document

### Current model:
###   Abstract syntax trees exist.
###   Some nodes have scopes as fields.
###     These scopes store dictionaries of name->symbol mappings.
###     But initially, they are empty.
###   Some nodes have varrefs (symbols) as fields.
###     But initially, they all refer to unique auto varrefs.
###   A SymtabBuilder is run to recompute all scope information from only the non-scope information.
###     Varrefs are unified based on name and location. Varref mappings are added to scopes.
###     Pattern stuff is done
###   If the tree is modified in any way, scope information is not automatically maintained.
###     It should be recomputed by running SymtabBuilder again from the root.
###   

### Ideas:
### - Might want to have symbols store their defining node and occurrences for convenience.
### It's not like we have to maintain this information, since we discard everything and run
### SymtabBuilder again (sorta). It could be useful if e.g. we want to get rid of vardef
### nodes for deleted symbols manually.
### - Should have predefined symbols for builtins
###



import itertools

import common
import darkitast as dka
import darhiast as dha

class ScopeSystemError(common.InternalError):
    """Internal problem with scope system."""
    pass

class ScopeError(common.ProgramError):
    """Scope problem in user program."""
    pass

# Counter for fresh non-set variables and suffixes.
freshvar_uid = common.UID(100, 3)
# Counter for fresh set variables.
freshsetvar_uid = common.UID(1, 1)
# Counter for fresh function symbols.
freshfunc_uid = common.UID(10, 2)

def getFreshNSymbol():
    uid = next(freshvar_uid)
    sym = dha.VSymbol('_v' + uid)
    sym.uid = uid
    return sym

def getFreshSSymbol():
    uid = next(freshsetvar_uid)
    sym = dha.VSymbol('S_' + uid)
    sym.uid = uid
    return sym

def getFreshSuffix():
    return next(freshvar_uid)

FLAG_AUTO = 'FLAG_AUTO'

def isauto(sym):
    return FLAG_AUTO in sym.flags

# Symbol kinds.
KIND_VSYM = 'KIND_VSYM'     # Variable symbol.
KIND_FSYM = 'KIND_FSYM'     # Function symbol.

def getKind(symbol):
    """Return a kind constant indicating the symbol type."""
    return (KIND_VSYM if isinstance(symbol, dha.VSymbol) else
            KIND_FSYM if isinstance(symbol, dha.FSymbol) else
            None)



def nodeHasSymtab(node):
    """Return whether or not a node defines its own scope, according to its type.
    This is irrespective of whether it has a Symtab or Scope object in the scope field."""
    return 'scope' in node._fieldnames

def nodeHasScope(node):
    """As above, but the scope must actually be a proper Scope object."""
    return 'scope' in node._fieldnames and isinstance(node.scope, Scope)

def getNodeScope(node):
    """Return the nearest lexically enclosing node with scope."""
    if nodeHasScope(node):
        return node.scope
    else:
        p = dka.getParentNode(node)
        return getNodeScope(p) if p is not None else None

class Scope(dka.Symtab):
    """Store and lookup symbols for a particular scope. The three kinds of symbols
    are kept in three different directories, although their symbols (and symbol names)
    should be disjoint."""
    
    def __init__(self, node):
        super().__init__()
        self.vars = {}
        self.funcs = {}
        self.node = node
    
    @property
    def parentscope(self):
        """Return the next outer scope, or None if there isn't any."""
        p = dka.getParentNode(self.node)
        return getNodeScope(p) if p is not None else None
    
    def _pickDomain(self, kind):
        """Retrieve the requested dictionary object to manipulate."""
        return {KIND_VSYM: self.vars,
                KIND_FSYM: self.funcs}[kind]
    
    def immediateLookupSymbol(self, name, kind):
        """Test for membership of a symbol of the given name and kind
        in this scope and this scope only."""
        assert(isinstance(name, str))
        domain = self._pickDomain(kind)
        if name in domain:
            return domain[name]
        else:
            return None
    
    def lookupSymbolAndScope(self, name, kind):
        """Lookup a symbol name in this scope and the enclosing scopes.
        Return both the symbol and the scope. Return None if it is not found."""
        assert(isinstance(name, str))
        domain = self._pickDomain(kind)
        if name in domain:
            return (self, domain[name])
        else:
            p = self.parentscope
            return p.lookupSymbolAndScope(name, kind) if p is not None else None
    
    def lookupSymbol(self, name, kind):
        """Lookup a symbol name and return the symbol, or None if it is not found."""
        val = self.lookupSymbolAndScope(name, kind)
        if val is None:
            return None
        else:
            scope, sym = val
            return sym
    
    # Lookup functions for the various symbol kinds.
    
    def lookupVSymbol(self, name):
        return self.lookupSymbol(name, KIND_VSYM)
    
    def lookupFSymbol(self, name):
        return self.lookupSymbol(name, KIND_FSYM)
    
    def _addSymbol(self, symbol, name, kind):
        """Add a symbol of a given kind to this scope."""
        domain = self._pickDomain(kind)
        if name not in domain:
            # FIXME: Shadowing disallowed for the moment.
            assert(self.lookupSymbol(name, kind) is None)
            domain[name] = symbol
        else:
            raise ScopeSystemError()
    
    # Symbol creation functions for the various symbol kinds.
    
    def _createSymbol(self, name, kind):
        sym = (dha.VSymbol(name) if kind is KIND_VSYM else
               dha.FSymbol(name) if kind is KIND_FSYM else
               None)
        self._addSymbol(sym, name, kind)
        return sym
    
    def _createVSymbol(self, name):
        sym = dha.VSymbol(name)
        self._addSymbol(sym, name, KIND_VSYM)
        return sym
    
    def _createFSymbol(self, name):
        sym = dha.FSymbol(name)
        self._addSymbol(sym, name, KIND_FSYM)
        return sym



### This visitor could be further simplified by either calling self.visit
### on replacement nodes before returning them, or, if that is too unsound or
### messy, adding some visitor mechanic that allows a node to be replaced
### in NodeTransformer before visit actually returns.
class SymtabBuilder(dka.NodeVisitor):
    """Given an abstract syntax tree, add appropriate scope and symbol
    datastructures, replacing the placeholder objects or any previous
    scope information."""
    
    def __init__(self):
        super().__init__()
        self.scopestack = []
    
    # The whole enter/leave scope stack thing is probably redundant,
    # what with getNodeScope(). We could just handle the outer-scoped
    # children before assigning a proper scope child to the node.
    # But this works so we'll keep it for now.
    
    def enterScope(self, node):
        """Push a scope on the stack. Set the scope attribute on the node."""
        scope = Scope(node)
        node.scope = scope
        self.scopestack.append(scope)
        return scope
    
    def leaveScope(self):
        """Pop a scope from the stack."""
        self.scopestack.pop()
    
    @property
    def currentscope(self):
        """Get the top of the stack."""
        return self.scopestack[-1]
    
    def lookupSymbol(self, symbol):
        """Lookup a symbol in scope, with the same name as the given symbol.
        Return None if it is not found."""
        scope = self.currentscope
        kind = getKind(symbol)
        return scope.lookupSymbol(symbol.name, kind)
    
    def isDefined(self, symbol):
        """Return whether or not a symbol with the given name is defined."""
        return self.lookupSymbol(symbol) is not None
    
    def lookupAndSetSymbol(self, node, attr):
        """Lookup a symbol by name, and update the node to use this symbol.
        The symbol must be in scope."""
        nodesym = getattr(node, attr)
        existsym = self.lookupSymbol(nodesym)
        if existsym is None:
            raise ScopeError('Symbol \'{}\' not defined'.format(nodesym.name))
        # If the node's symbol is marked auto, lookup a symbol in scope with
        # the same name and replace the node's symbol with it. Otherwise,
        # the node's symbol must be the same as the one in scope.
        if isauto(nodesym):
            setattr(node, attr, existsym)
        else:
            if nodesym is not existsym:
                raise ScopeError('Symbol \'{}\' conflicts with existing symbol'.format(nodesym.name))
    
    def defineSymbol(self, symbol):
        """Add a definition for a symbol. If it is already defined, a scope error is raised.
        If the symbol is auto, a new symbol is created with the same name. In either case,
        the defined symbol is returned."""
        scope = self.currentscope
        kind = getKind(symbol)
        
        # Check to make sure it's not already defined.
        existsym = scope.lookupSymbol(symbol.name, kind)
        if existsym is not None:
            raise ScopeError('Symbol \'{}\' multiply defined'.format(symbol.name))
        
        # If it's an auto symbol, use it but remove the auto flag,
        # otherwise, use the given one.
        if isauto(symbol):
            newsym = symbol
            symbol.flags.remove(FLAG_AUTO)
            scope._addSymbol(symbol, symbol.name, kind)
        else:
            scope._addSymbol(symbol, symbol.name, kind)
            newsym = symbol
        
        symbol.refresh()
        
        return newsym
    
    def defineAndSetSymbol(self, node, attr):
        """Add a definition as above, and update the node to use this symbol."""
        setattr(node, attr, self.defineSymbol(getattr(node, attr)))
    
    def lookupOrDefineAndSetSymbol(self, node, attr):
        """Lookup a symbol, and introduce it if it does not exist.
        Update the node to use this symbol either way."""
        nodesym = getattr(node, attr)
        if self.isDefined(nodesym):
            self.lookupAndSetSymbol(node, attr)
        else:
            self.defineAndSetSymbol(node, attr)
    
    def run(self, node):
        super().run(node)
    
    # Default behavior: Assume that all symbol occurrences must have been
    # defined before this use. If a definition is not found but the symbol
    # is auto-scoped and there is a symbol of the same name, replace the
    # occurrence with the existing symbol.
    ### FIXME: Is the order correct for visiting patterns, e.g. SetMatch and PatMatch?
    def generic_visit(self, node):
        scope = self.currentscope
        
        # Find the symbol fields.
        for fieldinfo, value in dka.iter_fields(node):
            if fieldinfo.isSymbolField():
                kind = getKind(value)
                ### FIXME: ignore function symbols for now;
                ### use-before-declare semantics is troublesome.
                if kind is KIND_FSYM:
                    self.lookupOrDefineAndSetSymbol(node, fieldinfo.name)
                    continue
                
                # Make sure the variable is defined.
                if not self.isDefined(value):
                    raise ScopeError('Variable \'{}\' used before defined'.format(value.name))
                
                self.lookupAndSetSymbol(node, fieldinfo.name)
        
        # Descend into children as normal.
        return super().generic_visit(node)
    
    def visit_Program(self, node):
        # Enter the global scope.
        globalscope = self.enterScope(node)
        
        # Descend into program.
        for decl in node.decls:
            self.visit(decl)
        if node.main:
            self.visit(node.main)
        
        self.leaveScope()
    
    def visit_VDecl(self, node):
        self.defineAndSetSymbol(node, 'id')
    
    def visit_FunctionDef(self, node):
        # Define the function symbol.
        self.lookupOrDefineAndSetSymbol(node, 'id')
        
        # Enter function scope.
        newscope = self.enterScope(node)
        
        # Define the arguments.
        for arg in node.args:
            self.defineAndSetSymbol(arg, 'id')
        
        # Descend into function body.
        self.visit(node.body)
        
        self.leaveScope()
    
    def visit_PatVar(self, node):
        if node.bnd is dha.P_UNKNOWN:
            if self.isDefined(node.id):
                node.bnd = dha.P_BOUND
                self.lookupAndSetSymbol(node, 'id')
            else:
                node.bnd = dha.P_UNBOUND
                self.defineAndSetSymbol(node, 'id')
        else:
            if node.bnd is dha.P_BOUND:
                self.lookupAndSetSymbol(node, 'id')
            elif node.bnd is dha.P_UNBOUND:
                ### "lookupOr": Keep in mind Assign nodes...
                self.lookupOrDefineAndSetSymbol(node, 'id')
    
    def visit_PatMatch(self, node):
        # Handle RHS first, then LHS.
        self.visit(node.iter)
        self.visit(node.target)
    
    def visit_PatMatchName(self, node):
        self.lookupAndSetSymbol(node, 'iter')
        self.visit(node.target)
    
    def visit_Assign(self, node):
        # Visit RHS first, then LHS.
        self.visit(node.value)
        self.visit(node.target)
    
    def visit_Reinit(self, node):
        self.lookupOrDefineAndSetSymbol(node, 'id')
    
    def visit_InvDef(self, node):
        self.visit(node.value)
        node.id.defnode = node
        self.defineAndSetSymbol(node, 'id')
    
    def visit_Match(self, node):
        # Create scope for (unexported) unbound variables.
        self.enterScope(node)
        
        self.generic_visit(node)
        
        self.leaveScope()
    
    def visit_SetComp(self, node):
        # Enter comprehension scope.
        self.enterScope(node)
        
        # Descend into enumerators.
        for enum in node.enums:
            self.visit(enum)
        
        # Descend into result expression.
        self.visit(node.elt)
        
        # Descend, in order to replace symbols and tag patterns.
        self.generic_visit(node)
        
        self.leaveScope()
    
    visit_RelSetComp = visit_SetComp

class PatternCleaner(dka.NodeVisitor):
    """Clean patterns by resetting their bnd attribute to unknown.
    This happens where boundedness should be inferred from whether
    or not the variable is already in scope. Notably, this does not
    include Assign nodes, where even an existing variable may appear
    unbound (to reassign to it)."""
    
    def visit_Assign(self, node):
        # Do not descend.
        pass
    
    def visit_PatVar(self, node):
        node.bnd = dha.P_UNKNOWN

def cleanPatterns(code):
    PatternCleaner().runBoth(code)
    return code

def buildSymtab(code, cleanpatterns = False):
    if cleanpatterns:
        cleanPatterns(code)
    SymtabBuilder().runBoth(code)
    return code



class SymbolGatherer(dka.NodeVisitor):
    """Collect symbols found in code."""
    
    def run(self, node):
        self.syms = []
        self.visit(node)
        return self.syms
    
    def visit(self, node):
        for field, value in dka.iter_fields(node):
            if field.isSymbolField():
                if value not in self.syms:
                    self.syms.append(value)
        self.generic_visit(node)

def gatherSymbols(code):
    return SymbolGatherer().runBoth(code)

class PatternSymbolGatherer(dha.PatternVisitor):
    """Collect pattern variables -- bound, unbound, or both."""
    
    def run(self, node, kinds):
        self.kinds = kinds
        self.syms = []
        self.visit(node)
        return self.syms
    
    def visit_PatVar(self, node):
        if node.bnd in self.kinds:
            self.syms.append(node.id)

def gatherPatSyms_kinds(code, kinds):
    return PatternSymbolGatherer().runBoth(code, kinds)

def gatherBoundPatSyms(code):
    return gatherPatSyms_kinds(code, {dha.P_BOUND})

def gatherUnboundPatSyms(code):
    return gatherPatSyms_kinds(code, {dha.P_UNBOUND})

def gatherPatSyms(code):
    return gatherPatSyms_kinds(code, {dha.P_BOUND, dha.P_UNBOUND, dha.P_UNKNOWN})

class InvSymbolGatherer(dka.NodeVisitor):
    def run(self, node):
        self.syms = []
        self.visit(node)
        return self.syms
    
    def visit(self, node):
        for field, value in dka.iter_fields(node):
            if field.isSymbolField() and value.hasflag(dha.FLAG_INV):
                if value not in self.syms:
                    self.syms.append(value)
        self.generic_visit(node)

def gatherInvSymbols(code):
    return InvSymbolGatherer().runBoth(code)

class SymbolReplacer(dka.NodeVisitor):
    """Replace symbols found in code."""
    
    # Although we're using NodeVisitor instead of NodeTransformer, the tree
    # is being mutated - just not in a way that rearranges nodes. 
    def run(self, node, symmapping, strict = False):
        self.symmapping = symmapping
        self.strict = strict
        self.visit(node)
    
    def visit(self, node):
        for field, value in dka.iter_fields(node):
            if field.isSymbolField():
                if value in self.symmapping:
                    setattr(node, field.name, self.symmapping[value])
                else:
                    if self.strict:
                        assert()
        self.generic_visit(node)

def replaceSymbols(code, symmapping, strict = False):
    SymbolReplacer().runBoth(code, symmapping, strict)

class SymbolExpander(dka.NodeTransformer):
    """Expand occurrences of Name nodes with expression subtrees."""
    
    def run(self, node, symmapping, strict = False):
        self.symmapping = symmapping
        self.strict = strict
        return self.visit(node)
    
    def generic_visit(self, node):
        for fieldinfo, value in dka.iter_fields(node):
            if fieldinfo.isSymbolField():
                if value in self.symmapping:
                    assert()
        return super().generic_visit(node)
    
    def visit_Name(self, node):
        if node.id in self.symmapping:
            return dka.copy(self.symmapping[node.id])
        else:
            if self.strict:
                assert()

def expandSymbols(code, symmapping, strict = False):
    return SymbolExpander().runBoth(code, symmapping, strict)



class ScopeSyntaxGenerator(dha.SyntaxGenerator):
    
    def __init__(self, show_symaddr = True, show_typestr = True,
                 show_defscopeid = True, show_ownscopeid = True,
                 show_boundedness = True, delim = ''):
        super().__init__(delim)
        self.show_symaddr = show_symaddr
        self.show_typestr = show_typestr
        self.show_defscopeid = show_defscopeid
        self.show_ownscopeid = show_ownscopeid
        self.show_boundedness = show_boundedness
    
    def sym_text(self, node, sym):
        # Determine symbol type.
        typestr, kind = (('V', KIND_VSYM) if isinstance(sym, dha.VSymbol) else
                         ('F', KIND_FSYM) if isinstance(sym, dha.FSymbol) else
                         ('X', None))
        
        # Get symbol name and address string.
        symname = str(sym)
        symaddr = hex(id(sym))
        
        # Find the defining scope for the symbol.
        defscope = None
        ctxtscope = getNodeScope(node)
        if ctxtscope is not None and kind is not None:
            val = ctxtscope.lookupSymbolAndScope(sym.name, kind)
            if val is not None:
                defscope, sym = val
        defscopeid = hex(id(defscope)) if defscope is not None else 'None'
        
        # If the symbol is a function, *and* it has a proper Scope child
        # (as opposed to a Symtab child), include its id as well.
        if dka.hasnodetype(node, dha.FunctionDef):
            if nodeHasScope(node):
                ownscopeid = '__' + hex(id(getNodeScope(node)))
            else:
                ownscopeid = '__None'
        else:
            ownscopeid = ''
        
        # If this is an enumvar, and we know whether it is bound or unbound, say which it is.
        if dka.hasnodetype(node, dha.PatVar):
            boundedness = ('?' if node.bnd is dha.P_UNKNOWN else
                           '=' if node.bnd is dha.P_BOUND else
                           '*' if node.bnd is dha.P_UNBOUND else
                           '!?!')
        else:
            boundedness = ''
        
        return ((boundedness if self.show_boundedness else '')
              + symname
              + (('_' + typestr) if self.show_typestr else '')
              + (('_' + symaddr) if self.show_symaddr else '')
              + (('$' + defscopeid) if self.show_defscopeid else '')
              + (ownscopeid if self.show_ownscopeid else ''))
    
    def visit_Program(self, node, ind):
        if nodeHasScope(node):
            ownscopeid = '__' + hex(id(getNodeScope(node)))
        else:
            ownscopeid = '__None'
        return ((ownscopeid if self.show_ownscopeid else '')
              + super().visit_Program(node, ind))
    
    def visit_PatVar(self, node, ind):
        return self.sym_text(node, node.id)
    
    def visit_SetComp(self, node, ind):
        if nodeHasScope(node):
            ownscopeid = '__' + hex(id(getNodeScope(node)))
        else:
            ownscopeid = '__None'
        return super().visit_SetComp(node, ind) + (ownscopeid if self.show_ownscopeid else '')

def genScopeSyntax(code, **kargs):
    return ScopeSyntaxGenerator(**kargs).runBoth(code)
