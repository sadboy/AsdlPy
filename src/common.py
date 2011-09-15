################################################################################
# common.py: Miscellaneous tools and data for the compiler.                    #
# Author: Jon Brandvein                                                        #
################################################################################

# Plan:
#  - this is major: separate tom's object-domain stuff from the tuple/pair-domain stuff.

# Todo:
# - syntax: should be able to update arbitrary expressions
#   - problem: need to figure out l-values then
#   - well, keeping in mind oids and object reference semantics, assignment
#   only makes sense when assigning to a variable or to a field, not to
#   the return value of a function or a randomly chosen element of a set.
#   That is, assignment is an operation on an l-value, not an object.
#   We don't have arrays or the like. Tuples are immutable and set elements
#   are not l-values. The only l-values I can think of are variables and fields.
#   So this issue is probably taken care of by allowing an AttrUpdate to take
#   an arbitrary expression.
#   - So this seems simple enough. SetUpdate in the obj domain can take arbitrary
#   expressions on the LHS, and in the tuple domain will just take a relation name.
#   Meanwhile, AttrUpdate can take arbitrary expressions on the LHS.
# - simplify resulting code
#   - in particular, fields generate redundant code for deleting values and the like.
# - dynamic object creation, extent operator
#   - perhaps reconsidering how objects are created, and allowing them to be explicitly deleted
# - local variable declaration, correct initialization
# - nesting order heuristic
#   - make more robust, less hackish
#   - possibly improve upon greedy algorithm by brute forcing to always choose minimal orders
# - cost estimation
# - constraints on comprehension expressions, ban unsafe negation
# - pattern matching with wildcards, equality constraints
#   - implement by rewriting as comprehensions
# - defining, clarifying, enforcing fixset requirements
# - make it clear that assignment's lhs must be fully unbound
# - input-language equivalent for Any, analogous to Match for NotEmpty
#   - or take the Patton approach and don't allow this -- require If
# - refactor a few areas using namedtuple
# - fixme: need global statement emitted into output python code
# - that thing about assigning update expressions to variables
#   in maintenance code, I probably don't need to do that at all
#   now that we have pattern expressions and expressions are deterministic
#   and side-effect-free.
# - should break up assertnodetype into smaller more readable stuff...
#   - More helper functions overall
# - multiple field td transformation
# - check to make sure the mapping passed to symbolreplacer is symbols not nodes, to catch bugs
# - comprehensions should have value semantics and should not be modeled using member.
#   so if you just iterate over it, we can optimize and do no copy, and same if it's
#   a nested comprehensions. but if you assign its result to a variable, this should
#   create a copy and the assignee variable can be modeled with member.
#   - for now, just have variables represent comprehensions directly and have the user
#     treat it as read-only, and don't transform these variables with member.
# - should have darkitnode autocopy if it would invalidate a tree somehow...
# - definitely need some system of giving hints to comprehensions w.r.t. join order

# Refactoring:
# - should replace some of those printtask-using functions in main
#   with something slightly smaller; maybe a decorator, and a better way
#   to do rebuildtree.
# - clean up this mess of a symbol hierarchy
# - clean up the pydarkit visitors with some more helper functions,
#   e.g. for constructing python function calls
# - improve how error handling is done, maybe get fancy with the stack trace print for convenience


# Ideas:
#  - separate program-fragment object to encapsulate ast with auxiliary information
#    - pass this to nodevisitor run(); especially nodetransformer, which can then do in-place
#      transformation of root without using return value 
#  - with regard to disowned ast nodes or whatever I called them, can have it so that
#    assigning a field always makes a copy of the root node being assigned but reuses
#    the children subtrees. That way, the original root node would not be stolen from
#    its parent so the parent wouldn't be invalidated. Only the original root node would
#    be invalidated. This enables the use case where a node is replaced with a tree that
#    contains the node (with the root copied).

# Fancy ideas:
#  - some kind of metasyntactic shorthand for constructing ast code with inline strings
#  - adding line number info to ast nodes, for better support in error messages

# Issues:
#  - attempts to iterate over non-set types when tags are not used
#  - break/continue not implemented; uglyness in transforming loops
#  - uglyness in loops as it is, when comprehensions are implemented

# Future features:
#  - aggregates
#  - patton output
#    - multiset rewriting
#  - possibly consider tom's method of doing tuples in the object-domain language
#  - something to maybe combine clauses when they overlap to a prefix of for loops
#    - like in the signals observer-pattern example where fields are transformed, not by
#      separate blocks of maintenance code for deleting the old value and adding the new,
#      but by a combined block of maintenance code with elses on the ifs.
#  - should add support for fields that cannot be rebound, to save on code space




import itertools
import collections



class DARkitError(Exception):
    """Base class for DARkit exceptions."""
    def __init__(self, msg = '', *args):
        super().__init__(msg.format(*args))

class InternalError(DARkitError):
    """Unexpected problem with the compiler. Subclasses of this exception
    provide more specific information about the fault, for example, whether
    it concerns an AST node's structure, or a violation of a method precondition.
    
    Generally, AssertionError is used in places where the invariant is simple
    or local to one piece of code."""

class ProgramError(DARkitError):
    """Static program error. This is used when a fault is found with the
    input program."""

class ProcessError(DARkitError):
    """Inability to perform transformation or operation. This is used if
    incrementalization fails, for instance."""



def setdict():
    """Create a dictionary whose default elements are sets."""
    return collections.defaultdict(lambda: set())

class OrderedSet():
    """A simple set that returns elements in the order they were added."""
    
    def __init__(self, seq = []):
        self.setdata = set()
        self.listdata = []
        self.update(seq)
    
    def add(self, item):
        if item not in self.setdata:
            self.setdata.add(item)
            self.listdata.append(item)
    
    def update(self, seq):
        for item in seq:
            self.add(item)
    
    def remove(self, item):
        if item not in self.setdata:
            raise KeyError
        self.setdata.remove(item)
        self.listdata.remove(item)
    
    def __iter__(self):
        return iter(self.listdata)
    
    def __contains__(self, item):
        return item in self.setdata
    
    def __len__(self):
        return len(self.setdata)



class UID:
    """A self-incrementing counter that yields numerical strings."""
    
    def __init__(self, start = 1, padding = 1):
        self.counter = start
        self.padding = padding
    
    def __iter__(self):
        return self
    
    def __next__(self):
        while True:
            num = self.counter
            self.counter += 1
            return str(num).rjust(self.padding, '0')
    
    def peek(self):
        return str(self.counter).rjust(self.padding, '0')

def genLetters():
    """A generator of characters in the range a-z."""
    return (chr(c) for c in range(ord('a'), ord('z') + 1))

def genNames():
    """A generator of strings a-z, aa-zz, ... ."""
    n = 1
    while True:
        lets = [genLetters() for _ in range(n)]
        seq = itertools.product(*lets)
        for item in seq:
            yield ''.join(item)
        n += 1



class DARkitState:
    """A singleton class that stores global state and settings
    concerning the run of the transformation. The settings are
    assigned values in main.py."""
    
    TUPLE_DOMAIN = 'TUPLE_DOMAIN'
    OBJECT_DOMAIN = 'OBJECT_DOMAIN'
    
    DOMAIN = ...
    STRICT = ...
    DSET = ...
    INCR = ...
    INLINE = ...
    IMPL = ...
    LEAVE_PD = ...
    REORDER_CLAUSES = ...
    PRUNE_REFCOUNT_PROPAGATION = ...
    USET = ...
    TAG = ...
    ALLPRED = ...

dks = DARkitState
