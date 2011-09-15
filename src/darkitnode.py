################################################################################
# darhinode.py: Code to construct and manage individual DARhi nodes.           #
# Author: Jon Brandvein                                                        #
################################################################################

# DARhi AST nodes represent the syntactic constructs of a DARhi program. Each specific node
# type is defined in a single ASDL file, which is used to generate class definitions. Those
# definitions are imported here for additional processing, and then re-exported. The primary
# purpose of this module, however, is to define the root of the AST class hierarchy, and all
# of the interesting node behavior that comes with it.


# Each node class has a _fields attribute derived directly from the ASDL. It holds a list of
# objects describing each field's name, type, and quantification. (For instance, the FunctionDef
# node has a field named "args", of type "argument" and quantification "list".) It is this
# attribute that gives the program tree its structure. Since manipulating ASTs is such a
# critical function, all suported updates to field values are strongly checked for consistency
# with the stated type/quantification constraints.

# List-valued fields always contain nodes, never primitives or other lists. Primitive types
# are assumed to be immutable; accordingly, they are shallow-copied.

# Field values are modified as if they were simple attributes. Singular fields can be assigned
# to, while list fields can be altered in several ways, including slicing. However, fields are
# actually implemented with descriptors, so that attempting to assign a value of the wrong type
# will result in an exception.


# In addition to _fields, each class has a _name attribute that is the same as its class __name__.
# Having a separate _name allows us to subclass the node types for implementation purposes, without
# conceptually interfering with the abstract grammar.


# Node instances have field attributes (described in _fields) and special attributes. Special
# attributes begin with a single underscore, and should not be directly used by external code.
# The two main special attributes are _parent and _valid.

# _parent is a reverse link containing the node's context: it's parent node, the field where it
# is stored, and its index (in the case of lists). _valid is True for all nodes that are well-
# formed with respect to their children - i.e., they have the correct type and correct parent link.

# When a child node is moved under a new parent, its old parent is invalidated: it still points
# to the child, but it should be considered as garbage. The child is said to be cannibalized.
# Cannibalization makes it easy to replace nodes without copying whole subtrees.



import itertools
import common

# Define __all__, add to it as we go.
__all__ = []

def public(object):
    """Decorator to make appending to __all__ concise."""
    __all__.append(object.__name__)
    return object



# Basic definitions.

# Symbol definition.

class Symtab:
    pass

class Symbol:
    def __init__(self, name, *, flags = set()):
        assert(isinstance(name, str))
        assert(len(name) > 0)
        self.name = name
        self.flags = flags
    
    def hasflag(self, flag):
        return flag in self.flags
    
    def refresh(self):
        pass
    
    def __str__(self):
        return '(' + self.name + ')'

# Quantifier enumerated constants.
QUANT_NORMAL = 'NORMAL'
QUANT_OPTIONAL = 'OPTIONAL'
QUANT_LIST = 'LIST'
QUANT_NONEMPTY = 'NONEMPTY'

__all__.extend(['Symtab', 'Symbol',
                'QUANT_NORMAL', 'QUANT_OPTIONAL', 'QUANT_LIST', 'QUANT_NONEMPTY'])



# Name/string helper functions.

def getName(obj, catchclass = False):
    """Retrieve _name if object is a node, _name if it's a node class and catchclass is False,
    __name__ concatenated with ' (class)' if it's a node class and catchclass is True, and
    its type __name__ if it's a primitive or primitive class."""
    if isinstance(obj, AST):
        return obj._name
    elif isinstance(obj, type) and issubclass(obj, AST):
        return obj.__name__ + ' (class)' if catchclass else obj._name
    else:
        return obj.__name__ if isinstance(obj, type) else obj.__class__.__name__

def genExpectedTypeStr(field):
    """Produce string name describing the type and its quantification."""
    name = getName(field.type)
    quantifier = field.quantifier
    if quantifier is QUANT_NORMAL:
        return name
    elif quantifier is QUANT_OPTIONAL:
        return name + ' option'
    elif quantifier is QUANT_LIST:
        return name + ' list'
    elif quantifier is QUANT_NONEMPTY:
        return 'non-empty ' + name + ' list'

# Various AST node type construction errors.
# Notice we use _name instead of __name__ so that the error messages
# are consistent if concrete nodes are subclassed for implementation reasons.

@public
class StructureError(common.InternalError):
    """Local structural issue with an AST node."""
    pass

@public
class NoFieldError(StructureError, AttributeError):
    """Attempt to access non-existent field.
    Since this is also an AttributeError, it can be raised from __getattribute__."""
    def __init__(self, node, fieldname):
        super().__init__('Node type {} has no field \'{}\'',
                         getName(node), fieldname)

@public
class FieldTypeError(StructureError):
    """Attempt to assign value of incorrect type to field."""
    def __init__(self, node, field, value):
        expectedtype = genExpectedTypeStr(field)
        super().__init__('Node type {} field \'{}\' should be of type {}, not {}',
                         getName(node), field.name, expectedtype, getName(value, catchclass = True))

@public
class NonEmptyError(StructureError):
    """Improper attempt to assign empty list."""
    def __init__(self, node, field):
        super().__init__('Node type {} field \'{}\' should be non-empty',
                         getName(node), field.name)

@public
class FieldListTypeError(StructureError):
    """Attempt to assign value of incorrect type as element of a list-valued field."""
    def __init__(self, node, field, value):
        expectedtype = genExpectedTypeStr(field)
        super().__init__('Node type {} field \'{}\' should be of type {}, '
                         'but found an element of type {}',
                         getName(node), field.name, expectedtype, getName(value, catchclass = True))

@public
class ConstructionError(StructureError):
    """Incorrect number of arguments, multiply-specified arguments,
    or missing non-default arguments."""
    def __init__(self, node, msg, *args):
        super().__init__('Constructing {}: {}',
                         getName(node), msg.format(*args))

@public
class ParentConsistencyError(StructureError):
    """Parent consistency error."""
    def __init__(self, parentnode, childnode, rightparent, gotparent):
        super().__init__('Parent consistency: parent {}, child {}, located at '
                         '{}:{}:{} but claims parent at {}:{}:{}',
                         parentnode, childnode,
                         id(rightparent.node), rightparent.fieldname, rightparent.index,
                         id(gotparent.node), gotparent.fieldname, gotparent.index)

@public
class FieldListDuplicationError(ParentConsistencyError):
    """Element appears more than once in field list."""
    pass



# Node hierarchy helpers.

@public
def hasnodetype(node, ntypes):
    """Return whether node's type is ntypes or in ntypes,
    if ntypes is a node class or collection respectively."""
    assert(isinstance(node, AST))
    if isinstance(ntypes, type):
        assert(issubclass(ntypes, AST))
        return isinstance(node, ntypes)
    else:
        for ntype in ntypes:
            assert(issubclass(ntype, AST))
            if isinstance(node, ntype):
                return True
        else:
            return False

class NodeTypeError(common.InternalError):
    """Expected different node type."""
    def __init__(self, node, ntypes):
        if isinstance(ntypes, type):
            s = ntypes.__name__
        else:
            s = 'one of {' + ', '.join(nt.__name__ for nt in ntypes) + '}'
        super().__init__('Expected {}, got {} instead',
                         s, node.__class__.__name__)

@public
def assertnodetype(node, ntypes):
    hastype = hasnodetype(node, ntypes)
    if not hastype:
        raise NodeTypeError(node, ntypes)
    return True



# Field and field helpers.

@public
class FieldInfo:
    """Wrapper class for field information. This should be considered immutable.
    
    The _fields attributes in the auto-generated classes are written as tuples,
    but get transformed into this. See do_NodeClassHackery, below."""
    
    def __init__(self, name, type, quantifier, asdltype):
        self.name = name
        self.type = type
        self.quantifier = quantifier
        self.asdltype = asdltype
    
    def __eq__(self, obj):
        return (isinstance(obj, FieldInfo) and
                self.name == obj.name and
                self.type is obj.type and
                self.quantifier is obj.quantifier)
    
    def __str__(self):
        return self.name
    
    def isNodeField(self):
        """Return whether field has node type (as opposed to primitive)."""
        return issubclass(self.type, AST)
    
    def isSymbolField(self):
        """Return whether field has symbol type."""
        return issubclass(self.type, Symbol)
    
    def isSingularField(self):
        """Return whether field is singular."""
        return (self.quantifier is QUANT_NORMAL or
                self.quantifier is QUANT_OPTIONAL)
    
    def isListField(self):
        """Return whether field is list-valued."""
        return (self.quantifier is QUANT_LIST or
                self.quantifier is QUANT_NONEMPTY)

def mangle(fieldname):
    """Return the mangled, actual name of an attribute that contains a field.
    The name in _fields is actually a descriptor that manipulates the mangled
    attribute."""
    return '_f_' + fieldname

@public
def isNode(obj):
    """Return whether obj is a DARkit AST node."""
    return isinstance(obj, AST)

@public
def isFieldList(obj):
    """Return whether obj is a field list of a node.
    (Not to be confused with method isListField above.)"""
    return isinstance(obj, FieldList)



# Parent and parent helpers.

@public
class Parent:
    """Wrapper class for parent information. This should be considered immutable."""
    
    def __init__(self, node = None, field = None, index = None):
        self.node = node
        self.field = field
        self.index = index
    
    def __eq__(self, obj):
        return (isinstance(obj, Parent) and
                self.node is obj.node and
                self.field == obj.field and
                self.index == obj.index)
    
    @property
    def fieldname(self):
        return self.field.name if self.field is not None else None
    
    def __str__(self):
        return '({}, {}, {})'.format(
            hex(id(self.node)) if self.node is not None else 'None',
            self.fieldname, self.index)

# The "None" of parenthood.
nilparent = Parent()
__all__.append('nilparent')



# Other helpers.

def checkValue(value, node, field):
    """Check that a value is appropriate for a field.
    Raise an exception if it is not.""" 
    # Handle list fields.
    if field.isListField() and isFieldList(value):
        # All the field lists assigned to a field should
        # have been created specifically for that node.
        assert(value.node == node)
        assert(value.field == field)
        # Check each element's type.
        for element in value:
            checkElementValue(element, node, field)
        return
    
    # Handle singular fields.
    else:
        # Allow omission if optional.
        if (field.quantifier is QUANT_OPTIONAL and
            value is None):
            return
        # Check type.
        if not isinstance(value, field.type):
            raise FieldTypeError(node, field, value)
        return

def checkElementValue(element, node, field):
    """Check that a field list element value is appropriate.
    Raise an exception if it is not."""
    if not isinstance(element, field.type):
        raise FieldListTypeError(node, field, element)



# Exported wrapper functions for underscore-prefixed methods.

@public
def getFields(node):
    return list(node._fields)

@public
def getFieldNames(node):
    return node._fieldnames

@public
def getFieldInfo(node, fieldname):
    return node._getFieldInfo(fieldname)

@public
def detatch(node):
    node._detach()

@public
def invalidate(node):
    node._invalidate()

@public
def isvalid(node):
    return node._valid

@public
def getParent(child):
    return child._parent

@public
def getParentNode(child):
    return child._parent.node

@public
def getParentField(child):
    return child._parent.field

@public
def getParentFieldName(child):
    return child._parent.fieldname

@public
def getParentIndex(child):
    return child._parent.index



# List-valued attributes are instances of this FieldList class.

class FieldList(list):
    """Maintains the invariants that the elements of a field list are of the
    correct type and have the correct parent information. The elements can be
    manipulated using the usual list functions, including slicing."""
    
    def __init__(self, node, field, sequence = []):
        super().__init__(sequence)
        self.node = node
        self.field = field
        self.rebuildElements()
    
    def rebuildElements(self):
        """Make the list consistent again after arbitrary modification,
        or raise an error. All nodes are cannibalized from their old
        parents."""
        # Make sure we're not violating the non-empty constraint.
        if (self.field.quantifier is QUANT_NONEMPTY and
            len(self) == 0):
            raise NonEmptyError(self.node, self.field)
        
        for i, item in enumerate(self):
            # Check element type.
            checkElementValue(item, self.node, self.field)
            # Set up parent information.
            item._moveto(Parent(self.node, self.field, i))
        
        # Make sure there are no duplicate references in the list
        # (by checking for index inconsistencies).
        for i, item in enumerate(self):
            if item._parent.index != i:
                raise FieldListDuplicationError(
                    self.node, item,
                    Parent(self.node, self.field, i),
                    Parent(item._parent.node, item._parent.field, item._parent.index))
        
        # Call the attach callbacks.
#        for item in self:
#            item._attach_callback()
    
    def detachElements(self):
        """Wipe out parent information for each item."""
        for element in self:
            element._detach()

# This hackery programmatically creates method overrides to intercept all updates to
# FieldLists, assuming that the below list of mutating methods is exhaustive.
# Sorry. At least I didn't use eval().
def do_FieldListHackery():
    # Functions that update the list's value.
    listfuncs = ['__setitem__', '__delitem__',
                 'append', 'extend', 'insert', 'pop', 'remove',
                 'sort']
    # The value of func is copied into this closure.
    def closure():
        # Get the appropriate unbound method in the base class (list).
        # (Caution: two-argument super is very different from one-argument super.)
        parentfunc = getattr(super(FieldList, FieldList), func)
        def hookedfunc(self, *args, **kargs):
            # First clear the parent information in all existing elements.
            self.detachElements()
            # Call the base class method.
            parentfunc(self, *args, **kargs)
            # Now rebuild the list from scratch.
            # The net effect is that anything that's removed will have its parent
            # info cleared, and anything that remains will be cannibalized from
            # nilparent (which is fine).
            self.rebuildElements()
        return hookedfunc
    
    for func in listfuncs:
        setattr(FieldList, func, closure())

# On the plus side, I'll be well prepared if Python 9.0 has dozens of
# new mutating list methods.
do_FieldListHackery()



# The big kahuna.

@public
class AST:
    """This class is the root of the DARkit AST hierarchy. It is responsible for
    ensuring that node objects are properly constructed with respect to the
    _fields class attribute specified in their type."""
    
    _rettype = None
    _teqs = []
    _inhtvars = []
    _ftvars = []
    _t = None
    
    def __init__(self, *args, **kargs):
        """Construct a node by initializing its _parent to nilparent,
        setting its children fields, and setting _valid to True.
        Children fields can be passed in by position or keyword,
        the same as Python's calling semantics."""
        
        # Be mixin-friendly.
        super().__init__()
        
        # Unpack arguments. This follows Python's calling semantics.
        
        # First, create a list of unfilled slots, one per formal.
        Unfilled = type('Unfilled', (), {})
        fields = self._fields
        slots = list(itertools.repeat(Unfilled, len(fields)))
        
        # Assign the positional arguments to the first slots.
        largs = len(args)
        if (largs > len(slots)):
            raise ConstructionError(self,
                'takes {} argument(s), got {}',
                len(fields), largs)
        slots[0:largs] = args
        
        # Assign the keyword arguments.
        for name, value in kargs.items():
            for i, field in enumerate(fields):
                if field.name == name:
                    if slots[i] == Unfilled:
                        slots[i] = value
                    else:
                        raise ConstructionError(self,
                            'field \'{}\' specified more than once',
                            field.name)
                    break
            else:
                raise ConstructionError(self,
                    'got non-existent field \'{}\'',
                    name)
        
        # Make sure nothing's left unfilled, except optionals.
        for i, (slot, field) in enumerate(zip(slots, fields)):
            if slot == Unfilled:
                if field.quantifier is QUANT_OPTIONAL:
                    slots[i] = None
                else:
                    raise ConstructionError(self,
                        'missing required field \'{}\'',
                        field.name)
        
        # Initialize parent information to None.
        self._parent = nilparent
        
        # Set up initial (invalid) field values.
        self._valid = False
        for field in fields:
            setattr(self, mangle(field.name), None)
        
        # Set fields to their real values.
        for slot, field in zip(slots, fields):
            setattr(self, field.name, slot)
        
        # Set valid flag to True.
        self._valid = True
    
    def _invalidate(self):
        """Set _valid to False, effectively making this node garbage."""
        self._valid = False
    
    def _detach(self):
        """Wipe out parent information."""
        self._parent = nilparent
    
    def _cannibalize(self):
        """Wipe out parent information, but first invalidate the parent.
        This is used when the child is being reused but the parent is
        effectively discarded."""
        if self._parent is not nilparent:
            self._parent.node._invalidate()
        self._detach()
    
    def _moveto(self, parent):
        """Canibalize and specify the new parent at once."""
        self._cannibalize()
        self._parent = parent
    
    def __getattr__(self, name):
        # Assume non-underscore-prefixed names are attempted field accesses.
        if len(name) > 0 and name[0] != '_':
            raise NoFieldError(self, name)
        else:
            raise AttributeError()
    
    def _setField(self, fieldname, value):
        """Change the value of a field. Make the magic happen."""
        field = self._getFieldInfo(fieldname)
        oldvalue = getattr(self, mangle(field.name))
        
        # Clear the old value's parent if applicable.
        # This is done before handling the new value, in case the
        # new and old values overlap.
        if isNode(oldvalue):
            oldvalue._detach()
        elif isFieldList(oldvalue):
            oldvalue.detachElements()
        
        if field.isSingularField():
            # Newvalue is simply the argument.
            newvalue = value
            if isNode(newvalue):
                # Canibalize the new value from its old parent, if one exists.
                # Set the new value's new parent.
                newvalue._moveto(Parent(self, field))
        else:
            if not isinstance(value, list):
                raise FieldTypeError(self, field, value)
            # Newvalue is a fresh FieldList object constructed from the given sequence.
            # This is only a shallow copy of the node elements themselves.
            # The elements will be cannibalized from their old parents.
            # The attach callback is called for each node upon list construction.
            newvalue = FieldList(self, field, value)
        
        # Check newvalue's type, quantification.
        checkValue(newvalue, self, field)
        
        # Apply the new value.
        setattr(self, mangle(field.name), newvalue)
    
    def __str__(self):
        return ('{}({})'.format(
                self.__class__.__name__,
                ','.join(str(getattr(self, f)) for f in self._fieldnames)))
    
    _fields = []
    
    @property
    def _fieldnames(self):
        """List all field names."""
        return [field.name for field in self._fields]
    
    def _getFieldInfo(self, name):
        """Associative access of field information by name."""
        for field in self._fields:
            if field.name == name:
                break
        else:
            raise NoFieldError(self, fieldname)
        return field
    
    @property
    def _syndom(self):
        """Get the syntactic domain type for this node, e.g.,
        whether it is a statement, expression, pattern, etc."""
        nodetype = self if isinstance(self, type) else self.__class__
        while True:
            base = nodetype.__bases__[0]
            base2 = base.__bases__[0]
            assert(issubclass(base2, AST))
            if base2 is AST:
                return nodetype
            else:
                nodetype = base



class FieldDescriptor:
    """A field descriptor is used to intercept updates to field attributes
    for consistency-checking purposes. Since it is a descriptor, it must
    be used as a class attribute."""
    
    def __init__(self, fieldname):
        self.fieldname = fieldname
    
    def __get__(self, instance, owner):
        # No special class attribute behavior.
        if instance is None:
            return self
        
        # Access the real field attribute under its mangled name.
        return getattr(instance, mangle(self.fieldname))
    
    def __set__(self, instance, value):
        # Invoke _setField to check the constraints and set the appropriate
        # real field attribute.
        instance._setField(self.fieldname, value)
    
    def __delete__(self, instance):
        # Disallow delete.
        pass



# Post-processing hackery on the automatically generated node classes.
# The _name attributes get set to the classes' names.
# The type names in _fields tuples get replaced with actual node types.
# The tuples themselves become FieldInfo objects.

# This step is needed because we can't directly refer to other classes
# within the code of the nodes file until they are declared. It is also
# useful for keeping the nodes file concise.

def do_NodeClassHackery(mod):
    # Collection of all node types.
    nodeclasses = {cl.__name__: cl
                   for cl in mod.__dict__.values()
                   if isinstance(cl, type) and issubclass(cl, AST)}
    
    for clname, cl in nodeclasses.items():
        # Set _name attributes.
        cl._name = clname
        
        # Substitute types for names, add descriptors.
        for i, (name, typename, quantifier) in enumerate(cl._fields):
            # Replace ASDL primitives with their PyObject equivalents,
            # and all others with their corresponding node class.
            if typename in mod.primitive_types:
                acttype = mod.primitive_types[typename]
            else:
                acttype = mod.__dict__[typename]
            cl._fields[i] = FieldInfo(name, acttype, quantifier, typename)
            # Add descriptor.
            setattr(cl, name, FieldDescriptor(name))
    
    # Set the __all__ field on the module to hold all the node classes.
    # Following this do_NodeClassHackery call with another import will
    # causes Pydef to properly include the nodes in autocompletion. Yay.
    mod.__all__ = list(nodeclasses.keys())
