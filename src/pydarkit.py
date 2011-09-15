################################################################################
# pydarhi.py: Convert abstract trees between DARhi and Python.                 #
# Author: Jon Brandvein                                                        #
################################################################################

import ast
import codegen
import common
import darkitast as dka
import darhiast as dha
import symtab as st
import computils as cu

class PythonToDARhiError(common.ProgramError):
    """Error converting input Python to internal DARhi."""
    pass

class DARhiToPythonError(common.InternalError):
    pass

# Nodes whose names are the same in Python and DARhi's grammar.
simple_nodes = {
    'And', 'Or',
    'Add', 'Sub', 'Mult', 'Div', 'Mod',
    'Not', 'UAdd', 'USub',
    'Eq', 'NotEq', 'Lt', 'LtE', 'Gt', 'GtE',
    'In', 'NotIn'}

AUTO = st.FLAG_AUTO

def genVSym(name):
    return dha.VSymbol(name, flags = {AUTO})

def genFSym(name):
    return dha.FSymbol(name, flags = {AUTO})

def genCompSym(name):
    return cu.CompSymbol(name, flags = {AUTO})

# This is one of the few visitors that does not traverse a DARkit tree
# and therefore does not derive from darkitast.NodeVisitor.
class PythonToDARhiImporter(ast.NodeVisitor):
    """Convert a Python abstract syntax tree into a DARhi one."""
    
    # An inpattern flag tracks whether we are currently parsing a pattern.
    # Patterns may only contain tuples and variables, not arbitrary
    # expressions. Furthermore, they yield PatTuple and PatVar nodes rather
    # than Tuple and Name nodes.
    
    def run(self, node, strict, objectdomain):
        self.strict = strict
        self.objectdomain = objectdomain
        
        self.inpattern = False
        
        return self.visit(node)
    
    def visit(self, node):
#        # Make sure patterns are simple.
        if (self.inpattern and
            not (isinstance(node, ast.Tuple) or
                 isinstance(node, ast.Name))):
            self.inpattern = False
            val = self.visit(node)
            self.inpattern = True
            return dha.PatExpr(val)
#            raise PythonToDARhiError('Invalid pattern expression')
        
        return super().visit(node)
    
    def generic_visit(self, node):
        # If this node is simple, it can be replaced trivially.
        name = node.__class__.__name__
        if name in simple_nodes:
            return dha.__dict__[name]()
        else:
            # Otherwise, we don't handle this node type.
            raise PythonToDARhiError('Unhandled node type \'{}\'',
                                     node.__class__.__name__)
    
    def module_helper(self, mod):
        """Separately process variable declarations, function definitions,
        and the main body."""
        stmts = mod.body
        
        decls, body = self.decls_helper(stmts)
        main = self.stmtlist_helper(body)
        
        return dha.Program(decls, main, dka.Symtab())
    
    def decls_helper(self, stmtlist):
        """Extract and process the declarations at the beginning of stmtlist,
        and return a pair of a list of the resulting nodes and the remaining
        list of unprocessed statements."""
        decls = []
        body = []
        
        for i, stmt in enumerate(stmtlist):
            if isinstance(stmt, ast.Expr):
                if not isinstance(stmt.value, ast.Name):
                    raise PythonToDARhiError('Invalid declaration')
                decls.append(dha.VDecl(genVSym(stmt.value.id)))
            
            elif isinstance(stmt, ast.Assign):
                if not (len(stmt.targets) == 1 and
                        isinstance(stmt.targets[0], ast.Name) and
                        isinstance(stmt.value, ast.Name)):
                    raise PythonToDARhiError('Invalid declaration')
                if stmt.value.id == 'fixset':
                    s = genVSym(stmt.targets[0].id)
                    s.fixset = True
                    decls.append(dha.VDecl(s))
                else:
                    raise PythonToDARhiError('Invalid declaration')
            
            elif isinstance(stmt, ast.FunctionDef):
                if stmt.name == 'main':
                    body = stmt.body
                    break
                else:
                    decls.append(self.func_helper(stmt))
            
            elif (isinstance(stmt, ast.If) and
                  stmt.orelse == [] and
                  isinstance(stmt.test, ast.Compare) and
                  len(stmt.test.ops) == len(stmt.test.comparators) == 1 and
                  isinstance(stmt.test.ops[0], ast.Eq) and
                  isinstance(stmt.test.left, ast.Name) and
                  stmt.test.left.id == '__name__' and
                  isinstance(stmt.test.comparators[0], ast.Str) and
                  stmt.test.comparators[0].s == '__main__'):
                body = stmt.body
            
            else:
                raise PythonToDARhiError('Invalid top-level node')
        
        return (decls, body)
    
    def func_helper(self, func):
        """Process a function definition node. Python FunctionDef nodes are statements,
        while in DARhi they are top-level. Therefore, we use this helper at the top-level
        and have visit_FunctionDef raise an error."""
        # Extract all the junk, make sure we're dealing with nothing but arg names.
        a = func.args
        if not ((a.kwonlyargs == a.defaults == a.kw_defaults == []) and
                (a.vararg is a.varargannotation is a.kwarg is a.kwargannotation is None)):
            raise PythonToDARhiError('Unsupported function definition features used')
        
        return dha.FunctionDef(genFSym(func.name),
                               [dha.Argument(genVSym(arg.arg)) for arg in a.args],
                               self.stmtlist_helper(func.body),
                               dka.Symtab())
    
    def stmtlist_helper(self, stmtlist):
        """Convert a list of Python stmt nodes into a DARhi Block node."""
        # Convert each statement and filter out the None returns.
        stmts = [val for val in (self.visit(stmt) for stmt in stmtlist)
                     if val is not None]
        
        # Return a block of these new statements, or None if the list is empty.
        return dha.Block(stmts) if len(stmts) > 0 else None
    
    def selector_helper(self, iter):
        if isinstance(iter, ast.Name):
            return dha.SelName(genVSym(iter.id))
        elif isinstance(iter, ast.Attribute):
            path = self.selector_helper(iter.value)
            if path is False:
                return False
            else:
                return dha.SelAttr(path, iter.attr)
        else:
            return False
    
    def generators_helper(self, generators):
        """Turn Python's structure for comprehension "generators" into enumerators."""
        if len(generators) == 0:
            raise PythonToDARhiError('Empty generator list in comprehension')
        
        # Convert each enumerator.
        enums = []
        conds = []
        for gen in generators:
            # Handle Fors.
            if self.objectdomain:
                target = self.pattern_helper(gen.target)
                if not (isinstance(gen.iter, ast.Name) or
                        isinstance(gen.iter, ast.Attribute)):
                    raise PythonToDARhiError('Invalid enumerator')
                iter = self.selector_helper(gen.iter)
                assert(iter is not False)
                enums.append(dha.AttrEnum(target, iter))
            
            else:
                target = self.pattern_helper(gen.target)
                if not isinstance(gen.iter, ast.Name):
                    raise PythonToDARhiError('Invalid enumerator')
                iter = genVSym(gen.iter.id)
                enums.append(dha.RelEnum(target, iter))
            
            # Handle attached Ifs.
            for cond in gen.ifs:
                # If of the form "pattern [not] in selector",
                # turn into an enumerator
                if (isinstance(cond, ast.Compare) and
                    len(cond.ops) == len(cond.comparators) == 1 and
                    (isinstance(cond.ops[0], ast.In) or
                     isinstance(cond.ops[0], ast.NotIn)) and
                     self.selector_helper(cond.comparators[0])):
                    
                    if self.objectdomain:
                        target = self.pattern_helper(cond.left)
                        iter = self.selector_helper(cond.comparators[0])
                        if isinstance(cond.ops[0], ast.In):
                            enums.append(dha.AttrEnum(target, iter))
                        else:
                            enums.append(dha.NegAttrEnum(target, iter))
                    else:
                        target = self.pattern_helper(cond.left)
                        assert(isinstance(cond.comparators[0], ast.Name))
                        iter = cond.comparators[0].id
                        if isinstance(cond.ops[0], ast.In):
                            enums.append(dha.RelEnum(target, iter))
                        else:
                            enums.append(dha.RelNegEnum(target, iter))
                # Otherwise, handle as a normal condition.
                else:
                    conds.append(self.visit(cond))
        
        return enums, conds
    
    def pattern_helper(self, tree):
        """Descend into tree, having enabled the inpattern flag."""
        self.inpattern = True
        result = self.visit(tree)
        self.inpattern = False
        return result
    
    def call_helper(self, call, isstmt):
        """Process a function or procedure call."""
        # Check that no fancy features are used.
        if not ((call.keywords == []) and
                (call.starargs is call.kwargs is None)):
            raise PythonToDARhiError('Invalid function call')
        
        args = [self.visit(arg) for arg in call.args]
        
        # Check that the LHS is simple.
        if isinstance(call.func, ast.Name):
            func = genFSym(call.func.id)
            nodetype = dha.CallProc if isstmt else dha.CallFunc
            return nodetype(func, args)
        
        else:
            raise PythonToDARhiError('Invalid function call')
    
    def visit_Module(self, node):
        return self.module_helper(node)
    
    def visit_FunctionDef(self, node):
        raise PythonToDARhiError('Function definitions must be top-level')
    
    def visit_Return(self, node):
        return dha.Return(self.visit(node.value))
    
    def visit_Assign(self, node):
        if len(node.targets) != 1:
            raise PythonToDARhiError('Invalid assignment')
        
        if isinstance(node.targets[0], ast.Name):
            sym = genVSym(node.targets[0].id)
            
            # Handle variable reinitialization to a new object.
            if (isinstance(node.value, ast.Name) and
                node.value.id == 'new'):
                return dha.Reinit(sym)
            
#            if isinstance(node.value, ast.Attribute):
#                if not isinstance(node.value.value, ast.Name):
#                    raise PythonToDARhiError('Invalid assignment')
#                source = genVSym(node.value.value.id)
#                return dha.AttrRetrieval(sym, source,
#                                         node.value.attr)
#            else:
#                return dha.Assign(dha.PatVar(sym, dha.P_UNBOUND),
#                                  self.visit(node.value))
            
            return dha.Assign(dha.genUnboundVar(sym),
                              self.visit(node.value))
        
        elif isinstance(node.targets[0], ast.Attribute):
            sym = genVSym(node.targets[0].value.id)
            return dha.AttrUpdate(sym, node.targets[0].attr,
                                  self.visit(node.value))
        
        else:
            raise PythonToDARhiError('Invalid assignment')
    
    def visit_Delete(self, node):
        if not (len(node.targets) == 1 and
                isinstance(node.targets[0], ast.Attribute) and
                isinstance(node.targets[0].value, ast.Name)):
            raise PythonToDARhiError('Invalid delete')
        return dha.DelAttr(genVSym(node.targets[0].value.id),
                           node.targets[0].attr)
    
    def visit_For(self, node):
        target = self.pattern_helper(node.target)
        iter = self.visit(node.iter)
        body = self.stmtlist_helper(node.body)
        orelse = self.stmtlist_helper(node.orelse)
        
        if self.objectdomain:
            return dha.For(dha.PatMatch(target, iter), body, orelse)
        else:
            dka.assertnodetype(iter, dha.Name)
            return dha.For(dha.PatMatchName(target, iter.id), body, orelse)
    
    def visit_While(self, node):
        body = self.stmtlist_helper(node.body)
        orelse = self.stmtlist_helper(node.orelse)
        # Membership tests become pattern matches.
        if (isinstance(node.test, ast.Compare) and
            len(node.test.ops) == len(node.test.comparators) == 1 and
            isinstance(node.test.ops[0], ast.In)):
            left = self.visit(node.test.left)
            right = self.visit(node.test.comparators[0])
            
            if self.objectdomain:
                node = dha.PatWhile(dha.PatMatch(dha.valueToPattern(left), right),
                                    body, orelse)
            else:
                dka.assertnodetype(iter, dha.Name)
                return dha.PatWhile(dha.PatMatchName(dha.valueToPattern(left), right.id),
                                    body, orelse)
        else:
            test = self.visit(node.test)
            node = dha.While(test, body, orelse)
        
        return node
    
    def visit_If(self, node):
        body = self.stmtlist_helper(node.body)
        orelse = self.stmtlist_helper(node.orelse)
        
        # Membership tests become pattern matches.
        if (isinstance(node.test, ast.Compare) and
            len(node.test.ops) == len(node.test.comparators) == 1 and
            isinstance(node.test.ops[0], ast.In)):
            left = self.visit(node.test.left)
            right = self.visit(node.test.comparators[0])
            if self.objectdomain:
                case = dha.PatCase(dha.PatMatch(dha.valueToPattern(left), right),
                                   body)
            else:
                dka.assertnodetype(right, dha.Name)
                case = dha.PatCase(dha.PatMatchName(dha.valueToPattern(left, right.od)),
                                   body)
        
        else:
            test = self.visit(node.test)
            case = dha.CondCase(test, body)
        
        return dha.If([case], orelse)
    
    def visit_Assert(self, node):
        # Asserts are simply stripped out.
        return None
    
    def visit_Pass(self, node):
        return dha.Pass()
    
    def visit_Expr(self, node):
        # An "is" expression is an invariant definition.
        if isinstance(node.value, ast.Compare):
            cm = node.value
            if (isinstance(cm.left, ast.Name) and
                len(cm.ops) == 1 and
                isinstance(cm.ops[0], ast.Is)):
                sym = genCompSym(cm.left.id)
                value = self.visit(cm.comparators[0])
                if not dka.hasnodetype(value, dha.RelSetComp):
                    raise PythonToDARhiError('Invalid invariant definition')
                return dha.InvDef(sym, value)
            else:
                raise PythonToDARhiError('Standalone expression statement')
        
        # Otherwise, an expression node should be a call to a procedure.
        
        # Check that it's a call.
        if not isinstance(node.value, ast.Call):
            raise PythonToDARhiError('Standalone expression statement')
        call = node.value
        
        # Special attributed calls are used to express set updates.
        if isinstance(call.func, ast.Attribute):
            updatemap = {'add':     dha.UpAdd,
                         'remove':  dha.UpRemove,
                         'union':   dha.UpUnion,
                         'diff':    dha.UpDiff,
                         'clear':   dha.UpClear,
                         'copy':    dha.UpCopy}
            isclear = call.func.attr == 'clear'
            if (isinstance(call.func.value, ast.Name) and
                call.func.attr in updatemap):
                if len(call.args) != (0 if isclear else 1):
                    raise PythonToDARhiError('Invalid number of arguments to set update')
                mod = dha.UP_STRICT if self.strict else dha.UP_NONSTRICT
                return dha.SetUpdate(genVSym(call.func.value.id),
                                     updatemap[call.func.attr](mod),
                                     self.visit(call.args[0]) if not isclear else dha.Num(0))
        
        return self.call_helper(call, isstmt=True)
    
    def visit_Name(self, node):
        if not self.inpattern:
            if node.id == 'True':
                return dha.Bool(True)
            elif node.id == 'False':
                return dha.Bool(False)
            
            return dha.Name(genVSym(node.id))
        else:
            if node.id == '_':
                return dha.PatIgnore()
            else:
                return dha.PatVar(genVSym(node.id), dha.P_UNKNOWN)
    
    def visit_Num(self, node):
        return dha.Num(node.n)
    
    def visit_Str(self, node):
        return dha.Str(node.s)
    
    def visit_Tuple(self, node):
        if not self.inpattern:
            return dha.Tuple([self.visit(elt) for elt in node.elts])
        else:
            return dha.PatTuple([self.visit(elt) for elt in node.elts])
    
    def visit_BoolOp(self, node):
        if len(node.values) < 2:
            # This shouldn't be possible.
            raise PythonToDARhiError('Fewer than two arguments to boolean operator')
        
        return dha.BoolOp(self.visit(node.op),
                          [self.visit(v) for v in node.values])
    
    def visit_BinOp(self, node):
        return dha.BinOp(self.visit(node.left),
                         self.visit(node.op),
                         self.visit(node.right))
    
    def visit_UnaryOp(self, node):
        return dha.UnaryOp(self.visit(node.op),
                           self.visit(node.operand))
    
    def visit_Compare(self, node):
        # Make sure only simple comparisons are used.
        if len(node.comparators) > 1:
            raise PythonToDARhiError('Complex comparison used')
        
        # Turn In, Not In into Match nodes.
        op = self.visit(node.ops[0])
        if dka.hasnodetype(op, {dha.In, dha.NotIn}):
            target = self.pattern_helper(node.left)
            iter = self.visit(node.comparators[0])
            if self.objectdomain:
                code = dha.Match(dha.PatMatch(target, iter), dka.Symtab())
            else:
                dka.assertnodetype(iter, dha.Name)
                code = dha.Match(dha.PatMatchName(target, iter.id), dka.Symtab())
            if dka.hasnodetype(op, {dha.NotIn}):
                code = dha.UnaryOp(dha.Not(), code)
            return code
        
        else:
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            return dha.BinOp(left, op, right)
    
    def visit_SetComp(self, node):
        enums, conds = self.generators_helper(node.generators)
        elt = self.visit(node.elt)
        if self.objectdomain:
            return dha.SetComp(elt, enums, conds, dka.Symtab())
        else:
            return dha.RelSetComp(elt, enums, conds, dka.Symtab())
    
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            # Catch bool, and interpret it as a set emptyness check.
            if node.func.id == 'bool':
                if len(node.args) != 1:
                    raise PythonToDARhiError('Invalid call')
                iter = self.visit(node.args[0])
                if self.objectdomain:
                    return dha.Match(dha.PatMatch(dha.genUnboundVar(st.getFreshNSymbol()),
                                                  iter),
                                     dka.Symtab())
                else:
                    dka.assertnodetype(iter, dha.Name)
                    return dha.Match(dha.PatMatchName(dha.genUnboundVar(st.getFreshNSymbol()),
                                                      iter.id),
                                     dka.Symtab())
            
            # Catch hasattr.
            elif node.func.id == 'hasattr':
                if len(node.args) != 2:
                    raise PythonToDARhiError('Invalid call')
                if not isinstance(node.args[1], ast.Str):
                    raise PythonToDARhiError('Reflection not allowed in hasattr')
                return dha.HasAttr(self.visit(node.args[0]), node.args[1].s)
        
        elif isinstance(node.func, ast.Attribute):
            # Catch any.
            if node.func.attr == 'any':
                if len(node.args) != 0:
                    raise PythonToDARhiError('Invalid call')
                return dha.UnaryOp(dha.Any(), self.visit(node.func.value))
        
        return self.call_helper(node, isstmt=False)
    
    def visit_Attribute(self, node):
        return dha.Attribute(self.visit(node.value), node.attr)

def importPythonToDARhi(pysrc, strict, domain):
#    try:
#        pytree = ast.parse(pysrc)
#    except SyntaxError as err:
#        raise PythonToDARhiError('Syntax:\n' + err.msg)
    pytree = ast.parse(pysrc)
    return PythonToDARhiImporter().run(pytree, strict, domain is common.dks.OBJECT_DOMAIN)



class PythonExporter(dka.NodeVisitor):
    """Convert a DARhi tree into a Python one."""
    
    def generic_visit(self, node):
        name = node.__class__.__name__
        if name in simple_nodes:
            return ast.__dict__[name]()
        else:
            raise DARhiToPythonError('Unhandled node type \'{}\'',
                                     node.__class__.__name__)
    
    def stmtlist_helper(self, stmtlist):
        stmts = [val for val in (self.visit(stmt) for stmt in stmtlist)
                     if val is not None]
        return stmts
    
    def enums_helper(self, enums):
        generators = []
        
        for enum in enums:
            
            if dka.hasnodetype(enum, dha.EnumFor):
                target = self.visit(enum.target)
                iter = self.visit(enum.iter)
                generators.append(ast.comprehension(target, iter, []))
            
            elif dka.hasnodetype(enum, dha.EnumIf):
                assert(len(generators) > 0)
                target = self.visit(enum.target)
                iter = self.visit(enum.iter)
                generators[-1].ifs.append(
                    ast.Compare(target, [ast.In()], [iter]))
            
            else: assert()
        
        return generators
    
    def patmatch_helper(self, patmatch):
        target = self.visit(patmatch.target)
        
        if dka.hasnodetype(patmatch, dha.PatMatch):
            iter = patmatch.iter
        
        elif dka.hasnodetype(patmatch, dha.PatMatchName):
            iter = dha.Name(patmatch.id)
        
        elif dka.hasnodetype(patmatch, dha.PatMatchLookup):
            iter = dha.Lookup(patmatch.id, patmatch.key)
        
        else: assert()
        
        iter = self.visit(iter)
        
        return target, iter
    
    def visit_Program(self, node):
        decls = [self.visit(decl) for decl in node.decls]
        main = self.visit(node.main) if node.main else []
        return ast.Module(decls + main)
    
    def visit_Block(self, node):
        return self.stmtlist_helper(node.stmtlist)
    
    def visit_VDecl(self, node):
        kind = node.id.kind if node.id.kind is not None else 'new'
        val = ast.Call(ast.Name(kind, ast.Load()), [], [], None, None)
        return ast.Assign([ast.Name(node.id.name, ast.Load())],
                          val)
    
    def visit_FunctionDef(self, node):
        name = node.id.name
        args = ast.arguments([ast.arg(a.id.name, None) for a in node.args],
                             None, None, [], None, None, [], [])
        body = self.visit(node.body)
        return ast.FunctionDef(name, args, body, [], None)
    
    def visit_PatTuple(self, node):
        return ast.Tuple([self.visit(e) for e in node.elts], ast.Load())
    
    def visit_PatVar(self, node):
        if node.bnd is not dha.P_UNBOUND:
            raise DARhiToPythonError('Patterns must only contain unbound variables')
        
        return ast.Name(node.id.name, ast.Load())
    
    def visit_PatIgnore(self, node):
        return ast.Name('_', ast.Load())
    
    def visit_Return(self, node):
        val = self.visit(node.value) if node.value is not None \
                                     else None
        return ast.Return(val)
    
    def visit_CallProc(self, node):
        return ast.Expr(ast.Call(ast.Name(node.func.name, ast.Load()),
                                 [self.visit(a) for a in node.args],
                                 [], None, None))
    
    def visit_CallProcMeth(self, node):
        return ast.Expr(ast.Call(ast.Attribute(ast.Name(node.func.name, ast.Load()),
                                               node.attr, ast.Load()),
                                 [self.visit(a) for a in node.args],
                                 [], None, None))
    
    def visit_Assign(self, node):
        return ast.Assign([self.visit(node.target)],
                          self.visit(node.value))
    
    def visit_Reinit(self, node):
        return ast.Assign([ast.Name(node.id.name, ast.Load())],
#                          ast.Call(ast.Name('oid', ast.Load()),
                          ast.Call(ast.Name('new', ast.Load()),
                                   [], [], None, None))
    
    def visit_DelAttr(self, node):
        return ast.Delete([ast.Attribute(ast.Name(node.target.name, ast.Load()),
                                         node.attr, ast.Load())])
    
    def visit_SetUpdate(self, node):
        dka.assertnodetype(node.op, {dha.UpAdd, dha.UpRemove})
        op = 'add' if dka.hasnodetype(node.op, dha.UpAdd) \
                   else 'remove'
        return ast.Call(ast.Attribute(ast.Name(node.target.name, ast.Load()),
                                      op, ast.Load()),
                        [self.visit(node.value)],
                        [], None, None)
    
    def visit_RefUpdate(self, node):
        dka.assertnodetype(node.op, {dha.UpAdd, dha.UpRemove})
        func = 'incref' if dka.hasnodetype(node.op, dha.UpAdd) \
                        else 'decref'
        return ast.Call(ast.Attribute(ast.Name(node.target.name, ast.Load()),
                                      func, ast.Load()),
                        [self.visit(node.value)],
                        [], None, None)
    
    def visit_AttrUpdate(self, node):
        return ast.Assign([ast.Attribute(ast.Name(node.target.name, ast.Load()),
                                         node.attr, ast.Load())],
                          self.visit(node.value))
    
    def visit_MapUpdate(self, node):
        dka.assertnodetype(node.op, {dha.UpAdd, dha.UpRemove})
        op = 'add' if dka.hasnodetype(node.op, dha.UpAdd) \
                   else 'remove'
        return ast.Call(ast.Attribute(ast.Subscript(ast.Name(node.target.name, ast.Load()),
                                                    ast.Index(self.visit(node.key)),
                                                    ast.Load()),
                                      op, ast.Load()),
                        [self.visit(node.value)],
                        [], None, None)
    
    def visit_For(self, node):
        target, iter = self.patmatch_helper(node.match)
        return ast.For(target,
                       iter,
                       self.visit(node.body),
                       self.visit(node.orelse) if node.orelse else [])
    
    def visit_While(self, node):
        return ast.While(self.visit(node.cond),
                         self.visit(node.body),
                         self.visit(node.orelse) if node.orelse else [])
    
    def visit_If(self, node):
        conds = []
        bodies = []
        
        for case in node.cases:
            dka.assertnodetype(case, dha.CondCase)
            conds.append(self.visit(case.cond))
            
            bodies.append(self.visit(case.body))
        
        # Construct the tree of nested if/elifs inside out.
        tree = self.visit(node.orelse) if node.orelse else []
        for cond, body in zip(reversed(conds), reversed(bodies)):
            tree = [ast.If(cond, body, tree)]
        
        return tree[0]
    
    def visit_Pass(self, node):
        return ast.Pass()
    
    def visit_Comment(self, node):
        return codegen.Comment(node.text)
    
    def visit_Name(self, node):
        return ast.Name(node.id.name, ast.Load())
    
    def visit_Num(self, node):
        return ast.Num(node.n)
    
    def visit_Str(self, node):
        return ast.Str(node.s)
    
    def visit_Bool(self, node):
        return ast.Name('True' if node.b else 'False', ast.Load())
    
    def visit_Tuple(self, node):
        return ast.Tuple([self.visit(e) for e in node.elts], ast.Load())
    
    def visit_BoolOp(self, node):
        return ast.BoolOp(self.visit(node.op),
                          [self.visit(v) for v in node.values])
    
    def visit_BinOp(self, node):
        if dka.hasnodetype(node.op,
                {dha.Add, dha.Sub, dha.Mult, dha.Div, dha.Mod}):
            return ast.BinOp(self.visit(node.left),
                             self.visit(node.op),
                             self.visit(node.right))
        elif dka.hasnodetype(node.op,
                {dha.Eq, dha.NotEq, dha.Lt, dha.LtE, dha.Gt, dha.GtE,
                 dha.In, dha.NotIn}):
            return ast.Compare(self.visit(node.left),
                               [self.visit(node.op)],
                               [self.visit(node.right)])
        else: assert()
    
    def visit_UnaryOp(self, node):
        if dka.hasnodetype(node.op, dha.NotEmpty):
            return ast.Call(ast.Name('bool', ast.Load()),
                            [self.visit(node.operand)],
                            [], None, None)
        
        elif dka.hasnodetype(node.op, dha.Any):
            return ast.Call(ast.Attribute(self.visit(node.operand),
                                          'any', ast.Load()),
                            [], [], None, None)
        
        else:
            return ast.UnaryOp(self.visit(node.op),
                               self.visit(node.operand))
    
    def visit_HasAttr(self, node):
        return ast.Call(ast.Name('hasattr', ast.Load()),
                        [self.visit(node.value), ast.Str(node.attr)],
                        [], None, None)
    
    def visit_GetRefCount(self, node):
        return ast.Call(ast.Attribute(ast.Name(node.id.name, ast.Load()),
                                      'getref', ast.Load()),
                        [self.visit(node.value)],
                        [], None, None)
    
    def visit_SetComp(self, node):
        return ast.SetComp(self.visit(node.elt),
                           self.enums_helper(node.enums))
    
    def visit_Match(self, node):
        # Handle empty using bool().
        # Make sure the LHS is all unbound.
        target, iter = self.patmatch_helper(node.match)
        return ast.Call(ast.Name('bool', ast.Load()),
                        [iter],
                        [], None, None)
    
    def visit_CallFunc(self, node): 
        return ast.Call(ast.Name(node.func.name, ast.Load()),
                        [self.visit(a) for a in node.args],
                        [], None, None)
    
    def visit_Attribute(self, node):
        return ast.Attribute(self.visit(node.value), node.attr, ast.Load())
    
    def visit_Lookup(self, node):
        return ast.Subscript(ast.Name(node.id.name, ast.Load()),
                             ast.Index(self.visit(node.key)),
                             ast.Load())
    
    def visit_CompatTuple(self, node):
        pat = self.visit(dha.patternToValue(node.pat))
        value = self.visit(node.value)
        return ast.Call(ast.Name('compat', ast.Load()),
                        [pat, value],
                        [], None, None)

def exportPython(tree):
    return PythonExporter().run(tree)

# Header to define utilities in Python target language.
# Includes reference-counted sets and dictionaries, and object creation tools.

pyheader_basic = \
"""import collections
import itertools
from time import clock
from random import *

"""

pyheader_rcset_unpruned = \
"""class rcset(set):
    def __init__(self, *args, **kargs):
        super().__init__(*args, **kargs)
        self.refcounts = collections.defaultdict(lambda: 0)
    
    def add(self, val):
        if val not in self:
            super().add(val)
        self.refcounts[val] += 1
    
    def remove(self, val):
        self.refcounts[val] -= 1
        if self.refcounts[val] == 0:
            super().remove(val)
            del self.refcounts[val]
    
    def any(self):
        return next(iter(self))
    
    def __hash__(self):
        return hash(id(self))
    
    def __str__(self):
        return '{' + ', '.join(str(elem) for elem in self) + '}'

class multidict(collections.defaultdict):
    def __init__(self):
        super().__init__(lambda: rcset())

"""

pyheader_rcset_asserts = \
"""class rcset(set):
    def __init__(self, *args, **kargs):
        super().__init__(*args, **kargs)
        self.refcounts = {}
    
    def add(self, val):
        assert(val not in self)
        assert(val not in self.refcounts)
        self.refcounts[val] = 0
        super().add(val)
    
    def remove(self, val):
        assert(val in self)
        assert(val in self.refcounts and self.refcounts[val] == 0)
        del self.refcounts[val]
        super().remove(val)
    
    def incref(self, val):
        assert(val in self)
        assert(val in self.refcounts)
        self.refcounts[val] += 1
    
    def decref(self, val):
        assert(val in self)
        assert(val in self.refcounts)
        self.refcounts[val] -= 1
    
    def getref(self, val):
        assert(val in self.refcounts)
        return self.refcounts[val]
    
    def any(self):
        return next(iter(self))
    
    def __hash__(self):
        return hash(id(self))
    
    def __str__(self):
        if hasattr(self, 'name'):
            return self.name
        else:
            return '{' + ', '.join((str(elem) + ':' + str(self.refcounts[elem]))
                                   for elem in self) + '}'
    
    __repr__ = __str__

class multidict(collections.defaultdict):
    def __init__(self):
        super().__init__(lambda: rcset())

"""

pyheader_rcset = \
"""class rcset(set):
    def __init__(self, *args, **kargs):
        super().__init__(*args, **kargs)
        self.refcounts = {}
    
    def add(self, val):
        self.refcounts[val] = 0
        super().add(val)
    
    def remove(self, val):
        del self.refcounts[val]
        super().remove(val)
    
    def incref(self, val):
        self.refcounts[val] += 1
    
    def decref(self, val):
        self.refcounts[val] -= 1
    
    def getref(self, val):
        return self.refcounts[val]
    
    def any(self):
        return next(iter(self))
    
    def __hash__(self):
        return hash(id(self))
    
    def __str__(self):
        return '{' + ', '.join(str(elem) for elem in self) + '}'

class multidict(collections.defaultdict):
    def __init__(self):
        super().__init__(lambda: rcset())

"""

pyheader_compat = \
"""_ = None
def compat(pat, value):
    if isinstance(pat, tuple) and isinstance(value, tuple):
        if len(pat) == len(value):
            return all(compat(p, v) for p, v in zip(pat, value))
        else:
            return False
    elif isinstance(pat, tuple) and not isinstance(value, tuple):
        return False
    else:
        return True

"""

pyheader_oids_od = \
"""def new():
    return rcset()
"""

pyheader_oids_td = \
"""def letters():
    return (chr(c) for c in range(ord('a'), ord('z') + 1))

def genOIDs():
    n = 1
    while True:
        lets = [letters() for _ in range(n)]
        seq = itertools.product(*lets)
        for item in seq:
            yield ''.join(item)
        n += 1

oids = genOIDs()
def new():
    return next(oids)

"""

def generatePython(tree):
    pyheader = pyheader_basic
    
    if not common.dks.PRUNE_REFCOUNT_PROPAGATION:
        pyheader += pyheader_rcset_unpruned
    else:
        pyheader += pyheader_rcset_asserts
    
    pyheader += pyheader_compat
    if common.dks.LEAVE_PD:
        pyheader += pyheader_oids_od
    else:
        pyheader += pyheader_oids_td
    
    tree = exportPython(tree)
    src = codegen.to_source(tree)
    src = pyheader + src
    return src
