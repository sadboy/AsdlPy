################################################################################
# darkitast.py: Utilities for manipulating a DARkit abstract syntax tree.      #
# Author: Jon Brandvein                                                        #
################################################################################

# The definitions contained in the darkitnode module are re-exported here.

# Each DARkit language defines node types to represent its syntactic concepts.
# Node types are distinguished primarily by the fields they have, which may be
# of primitive type, a particular node type, or a homogeneous list of nodes.
# The language defines both terminal nodes, which are instantiated to compose
# an AST, and non-terminal nodes, which are used to type-constrain fields.
# Terminal nodes inherit from non-terminals, which themselves inherit from
# a language-specific root, which itself inherits from darkitnode.AST. 

# For the sake of definite terminology, we can say a "field" is the class-wide information
# about the type of value allowed in a given attribute of a given node type; a "field value"
# is the value assigned to a field on an instance node; a "field element" is an element of
# a field value that is a list; and a "child" is a field value or field element (i.e., non-
# primitive value).

# Nodes enforce local integrity constraints whenever they are constructed or their field
# values are modified. Specifically, children must have consistent parent information
# pointing back to the containing node, and all field values must be of the proper type.
# Non-local constraints such as acyclicity are not automatically enforced there.

# When new nodes are constructed, they may cannibalize the children of old nodes, rendering
# the old nodes invalid. 

# This module contributes a visitor design pattern for traversing, transforming, copying,
# or otherwise manipulating node trees. Abstract visitor base classes, mixins, and simple
# specific concrete visitors are defined. The basic idea for such a pattern is inspired
# by Python's AST library, but these utilities are far more powerful.

### TODO: check above for accuracy



import itertools
import common
from darkitnode import *

class ASTError(common.InternalError):
    """Malformed AST error."""
    pass

def iter_fields(node):
    """Yield a fieldinfo, value tuple for each present field."""
    for fieldinfo in getFields(node):
        yield fieldinfo, getattr(node, fieldinfo.name)

def dump(val):
    """Print the node tree in function-call form."""
    if isNode(val):
        return str(val)
    elif isFieldList(val):
        return ('['
              + ','.join([dump(v) for v in val])
              + ']')
    elif isinstance(val, str):
        return '\'' + val + '\''
    elif val is None:
        return 'None'
    else:
        return '<Bad type: ' + str(type(val)) + '>'

def listifyValue(val):
    return ([] if val is None else
            val if isinstance(val, list) else
            [val])



# --- Visitor basics. ---

class BaseNodeVisitor:
    """An abstract base class for all visitors. The visit method should be overridden.
    The generic_visit method by default will just recursively visit all children."""
    
    def validateNode(self, node):
        """Make sure the node is in fact a node, and that it belongs to the
        expected (sub)language."""
        ### TODO: should probably also check node's _valid flag here, because it's easy,
        ### instead of only catching invalid nodes when checkTree is used.
        assert(isNode(node))
    
    def run(self, node, *args, **kargs):
        """Simply call the visit method. This is useful for overriding when the initial
        behavior needs to be changed without affecting the visit specialization for
        other instances of the root node."""
        return self.visit(node, *args, **kargs)
    
    def runSeq(self, code, *args, **kargs):
        """Call run on a sequence and produce a list result."""
        return [self.run(node, *args, **kargs) for node in code]
    
    def runBoth(self, code, *args, **kargs):
        """Call either run or runSeq as appropriate."""
        if isNode(code):
            return self.run(code, *args, **kargs)
        else:
            return self.runSeq(code, *args, **kargs)
    
    def visit(self, node, *args, **kargs):
        """Replace this with a strategy for dispatching to a specialized method
        based on the node's features."""
        self.validateNode(node)
        return self.generic_visit(node, *args, **kargs)
    
    # These might be unnecessary, so for simplicity I'll leave them out unless needed.
#    def visitSeq(self, code, *args, **kargs):
#        """Call visit on a sequence and produce a list result."""
#        return [self.visit(node, *args, **kargs) for node in code]
#    
#    def visitBoth(self, code, *args, **kargs):
#        """Call either visit or visitSeq as appropriate."""
#        if isNode(code):
#            return self.visit(code, *args, **kargs)
#        else:
#            return self.visitSeq(code, *args, **kargs)
    
    def generic_visit(self, node, *args, **kargs):
        """Visit all fields, including elements of lists. No return value."""
        for fieldinfo, value in iter_fields(node):
            if isFieldList(value):
                # We iterate over a copy of the value list, in case it is
                # modified during the traversal (for example, by NodeTransformer).
                for item in list(value):
                    self.visit(item, *args, **kargs)
            elif isNode(value):
                self.visit(value, *args, **kargs)
            else:
                pass

class ChainListMixin(BaseNodeVisitor):
    """Simple mixin to alter the behavior of running and visiting list input."""
    def runSeq(self, code, *args, **kargs):
        return list(itertools.chain(super().runSeq(code, *args, **kargs)))
    
#    def visitSeq(self, code, *args, **kargs):
#        return list(chain(super().runSeq(code, *args, **kargs)))



# --- Visitor base classes. ---

class NodeVisitor(BaseNodeVisitor):
    """Traverse the tree by dispatching to specializations of visit based on the node type.
    
    This can be used to construct a return value from the bottom up, but by default,
    BaseNodeVisitor's generic_visit just makes sure that children are covered in the
    order they're listed in the class's _fields list.
    
    Subclass and add visit_NODENAME methods. Override generic_visit if necessary."""
    
    def visit(self, node, *args, **kargs):
        """Dispatch to a visit_* method based on the node type. Call generic_visit if
        no method is found. Note that node type is decided by its _name attribute,
        not __name__, so implementation-derived node classes will not alter dispatch
        behavior."""
        self.validateNode(node)
        method = 'visit_' + node.__class__._name
        visitor = getattr(self, method, self.generic_visit)
        return visitor(node, *args, **kargs)

class WideNodeVisitor(NodeVisitor):
    """A generalization of the above visitor, wherein we search for a specialization
    that handles the node's whole syntactic domain type (a non-terminal in the ASDL),
    before falling back on its concrete type (a terminal). For example, visit_stmt,
    if this "wide" specialization exists, would be called before the "narrow" visit_Update.
    This makes it easier to intercept the processing of certain nodes."""
    
    def visit(self, node, *args, wide = True, **kargs):
        """If wide is True, dispatching works as described above. If it is False,
        this will only dispatch to concrete type specializations, as in the normal
        NodeVisitor. This allows a non-concrete type's handler to reinvoke visit
        on the same node and trigger the more specific concrete type handler instead."""
        if wide:
            method = 'visit_' + node._syndom._name
            visitor = getattr(self, method, None)
            if visitor is not None:
                return visitor(node, *args, **kargs)
        return super().visit(node, *args, **kargs)
    
    def dispatch(self, node, *args, **kargs):
        """Explicitly bypass the wide specialization."""
        return self.visit(node, wide = False, *args, **kargs)



# --- Transformers. ---

# The node transformation code is written in a mixin-friendly way so that
# it can be combined with other visitor strategies besides the standard
# node-type-based NodeVisitor. Most of the time classes will inherit from
# the non-mixin versions below.

class GeneralNodeTransformerMixin(BaseNodeVisitor):
    """Transform a tree by replacing children.
    
    For most uses, transform_ignorenone = True suffices. It only needs to
    be set False for code that deletes nodes without replacing them.
    
    This mixin class should appear before the visitor class in a derived
    type's bases list, to ensure that this visit method takes precedence."""
    
    def __init__(self, transform_ignorenone = False):
        super().__init__()
        self.transform_ignorenone = transform_ignorenone
    
    def transform_hook(self, newcontent, oldnode, parent):
        """This method is called whenever a structural change is made to the tree.
        The old node is generally discarded, but it may be useful."""
        pass
    
    ### The reason we need a return value is that replacing the top level node
    ### wouldn't do anything otherwise. What we really need is a way to encapsulate
    ### the tree inside an object, so replacing the toplevel node is just a matter
    ### of altering an attribute on that wrapping object.
#    def run(self, node, *args, **kargs):
#        # No return value.
#        self.visit(node, *args, **kargs)
    
    def visit(self, node, *args, transform_bypass = False, **kargs):
        """Call super().visit on a node, and replace the node with the result.
        For list fields, the result can either be a new list to splice in place
        of the old element, or a node to take the place of the element.
        
        No action is taken if None is returned and transform_ignorenone is True.
        This makes it easy to write visitors without having to return the argument
        node over all control paths.
        
        The method transform_hook is called whenever a structural change is made
        by this method - it is only skipped when ignoring a None, or when the same
        object is returned as was called on.
        
        If transform_bypass is True, all special behavior is suppressed and
        the call simply passes through to super().visit."""
        
        # This visitor is used frequently enough that an extra redundant check
        # at the beginning isn't a terrible thing.
        self.validateNode(node) 
        
        # If bypass is requested, just call the visit method.
        if transform_bypass:
            return super().visit(node, *args, **kargs)
        
        # Retrieve parent information.
        # This is done before the visit call in case the node is
        # moved to a subtree of the result.
        parent = getParent(node)
        parentnode = getParentNode(node)
        parentfieldname = getParentFieldName(node)
        parentindex = getParentIndex(node)
        
        # Invoke visit call.
        result = super().visit(node, *args, **kargs)
        
        # Take no action if result is None and we're ignoring it,
        # or if the result is the same object we started with.
        if ((result is None and self.transform_ignorenone) or
            (result is node)):
            return node
        
        # Perform the replacement.
        if parentnode is not None:
            if parentindex is None:
                setattr(parentnode, parentfieldname, result)
            else:
                # Replace None with empty list; wrap nodes in singleton lists.
                listresult = listifyValue(result)
                getattr(parentnode, parentfieldname)[parentindex:parentindex+1] = listresult
        
        # Invoke the hook.
        self.transform_hook(result, node, parent)
        
        # Return the result.
        return result
    
    def generic_visit(self, node, *args, **kargs):
        super().generic_visit(node, *args, **kargs)
        return node

class NodeTransformerMixin(GeneralNodeTransformerMixin):
    """Same as above, but set transform_ignorenone = True."""
    def __init__(self):
        super().__init__(transform_ignorenone = True)

class GeneralNodeTransformer(GeneralNodeTransformerMixin, NodeVisitor):
    """Combine NodeTransformerMixin with the standard type-based dispatch method."""
    pass

class NodeTransformer(NodeTransformerMixin, NodeVisitor):
    """Same as above, with transform_ignorenone = True."""
    pass



# --- Simple utilities. ---

class NodeTypeFinder(BaseNodeVisitor):
    """Return a set of all the types of nodes used."""
    
    def run(self, node):
        self.types = set()
        super().run(node)
        return self.types
    
    def generic_visit(self, node):
        self.types.add(node.__class__)
        super().generic_visit(node)

def findNodeTypes(code):
    return NodeTypeFinder().runBoth(code)

class NodeCopier(BaseNodeVisitor):
    """Copy a tree by generating new nodes from existing ones."""
    
    # This implementation may have issues when a node type is used both as a singular
    # and as a list-valued child field: which one should the visit specialization return?
    ### I'm no longer sure if I agree with / understand the above comment.
    
    def generic_visit(self, node):
        """Construct a new node with the field values obtained by recursing over the old
        fields. Non-nodes are shallow-copied, with the assumption that they are immutable.
        Lists are generally mapped element by element, but if None is returned the element
        is not copied, and if a list is returned it is spliced in."""
        # Determine new list of field values.
        children = []
        for fieldinfo, value in iter_fields(node):
            if isFieldList(value):
                newlist = []
                for item in value:
                    result = self.visit(item)
                    if result is None:
                        pass
                    elif isFieldList(result):
                        newlist.extend(result)
                    else:
                        newlist.append(result)
                children.append(newlist)
            elif isNode(value):
                children.append(self.visit(value))
            else:
                children.append(value)
        
        # Construction.
        newnode = node.__class__(*children)
        
        return newnode

def copy(code):
    return NodeCopier().runBoth(code)

def copier(code):
    stored = copy(code)
    return lambda: copy(stored)

class ParentError(ASTError):
    """Parent information inconsistent."""
    pass

class ValidityError(ASTError):
    """Invalid node found in tree."""
    pass

# Cycles can't easily develop anyway: attempting to set a node to be
# its own child would cause it to disown its parent, cutting it off
# from the rest of the tree.
class CyclicityError(ASTError):
    """Cycle found in tree."""
    pass

### TODO: might want to make a parent-passing nodevisitor class
class TreeChecker(BaseNodeVisitor):
    """Verify the consistency of a tree. Validate every node,
    and check for cycles."""
    
    def run(self, node):
        self.seen = set()
        
        # The first node should have a nil parent.
        self.visit(node, nilparent)
    
    def visit(self, node, parent):
        if parent != getParent(node):
            raise ParentError()
        
        if not isvalid(node):
            raise ValidityError()
        
        # Make sure we haven't seen this node before.
        if node in self.seen:
            raise CyclicityError()
        self.seen.add(node)
        
        self.generic_visit(node)
    
    def generic_visit(self, node, *args, **kargs):
        """Slightly modified version of generic visit that passes the parent information
        along for consistency checking."""
        for fieldinfo, value in iter_fields(node):
            if isFieldList(value):
                for i, item in enumerate(list(value)):
                    parent = Parent(node, fieldinfo, i)
                    self.visit(item, parent, *args, **kargs)
            elif isNode(value):
                parent = Parent(node, fieldinfo)
                self.visit(value, parent, *args, **kargs)
            else:
                pass

def checkTree(code):
    TreeChecker().runBoth(code)
