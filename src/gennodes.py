################################################################################
# gennodes.py: Generate Python 3k classes for DARkit abstract syntax tree      #
#              nodes, from an ASDL file.                                       #
# Author: Jon Brandvein                                                        #
# Note: This program must be run in Python 2.6 due to TPG's limitations.       #
################################################################################

import itertools
import tpg

class ASDLError(Exception):
    pass



# Parse the ASDL file and gather the information used to create Python definition code.
class ASDLReader(tpg.Parser):
    r"""
    separator spaces:   '\s+';
    separator comment1: '#.*';
    separator comment2: '--.*';
    
    # Keywords.
    token langkw:       'language';
    token primkw:       'primitive';
    
    token ident:        '[_a-zA-Z][_a-zA-Z0-9]*';
    
    # Symbols.
    token lpar:         '\(';
    token rpar:         '\)';
    token comma:        ',';
    token quant:        '\?|\*|\+';
    token or_:          '\|';
    token eq:           '=';
    token annstr:       '@.*?(@|\n)';
    
    # The ASDL file consists of a header and rules. The header specifies
    # the language name and some user-defined primitive types. The rules
    # are productions specifying a node hierarchy.
    
    START/v ->      Header/h Rules/r                $ v = (h, r)
                    ;
    
    Header/h ->     LangHead/lh                     $ h = (lh, [])
                    (PrimHead/th                    $ h[1].append(th)
                    )*
                    ;
    
    LangHead/h ->   langkw ident/l                  $ h = l
                                                    $ setRootName(l + 'Node')
                    ;
    
    PrimHead/h ->   primkw ident/p                  $ h = p
                    ;
    
    Rules/r ->      Rule                            $ r = Rule
                    (Rule                           $ r.extend(Rule)
                    )*
                    ;
    
    # Each non-terminal node extends the root for the language.
    
    Rule/r ->       ident/basecls                   $ a = []
                    (Ann/a
                    )?
                    eq                              $ r = [NodeInfo(basecls, rootname, [], a)]
                    Prods<basecls>                  $ r.extend(Prods)
                    ;
    
    Prods<b>/p ->   Prod<b>                         $ p = [Prod]
                    (or_ Prod<b>                    $ p.append(Prod)
                    )*
                    ;
    
    # Each terminal node extends its non-terminal node, and specifies its fields.
    
    Prod<b>/p ->    Node/n                          $ c, a = [], []
                    (lpar Fields/fs rpar            $ c = fs
                    )?
                    (Ann/a
                    )?
                                                    $ p = NodeInfo(n, b, c, a)
                    ;
    
    Node/n ->       ident/cls                       $ n = cls
                    ;
    
    Fields/fs ->    Field/f                         $ fs = [f]
                    (comma Field/f                  $ fs.append(f)
                    )*
                    ;
    
    Field/f ->      ident/type                      $ q = ''
                    (quant                          $ q = quant
                    )?
                    ident/name                      $ f = (name, type, q)
                    ;
    
    Ann/s ->                                        $ s = []
                    (annstr/a                       $ s.append(a)
                    )+
                    ;
    """

R_RT = 'R_RETTYPE'
R_TE = 'R_TYPEEQ'
R_IV = 'R_INHTVARS'
R_FV = 'R_FIELDTVARS'

class TypeReader(tpg.Parser):
    r"""
    separator spaces:   '\s+';
    separator at:       '@';
    
    token ident:        '[_a-zA-Z][_a-zA-Z0-9]*';
    
    token lpar:         '\(';
    token rpar:         '\)';
    token comma:        ',';
    token dot:          '\.';
    token star:         '\*';
    token eq:           '=';
    token langle:       '<';
    token rangle:       '>';
    token semicolon:    ';';
    
    START/rs ->     Rule/r                          $ rs = [r]
                    (semicolon Rule/r               $ rs.append(r)
                    )*
                    ;
    
    Rule/r ->       RetType/v                       $ r = (R_RT, v)
                  | TypeEq/v                        $ r = (R_TE, v)
                  | InhTVars/v                      $ r = (R_IV, v)
                  | FieldTVars/v                    $ r = (R_FV, v)
                    ;
    
    RetType/r ->    eq Type/r
                    ;
    
    TypeEq/r ->     Type/t1 eq Type/t2              $ r = (t1, t2)
                    ;
    
    InhTVars/r ->   langle TVarList/tvl rangle      $ r = tvl
                    ;
    
    FieldTVars/r -> ident/f
                    langle TVarList/tvl rangle      $ r = (f, tvl)
                    ;
    
    TVarList/tvl -> ident/v                         $ tvl = [v]
                    (comma ident/v                  $ tvl.append(v)
                    )*
                    ;
    
    Type/t ->       #ident/tt dot ident/a            $ t = ('@', (tt, a))
                    ident/v lpar TypeList/tl rpar   $ t = (v, tuple(tl))
                  | ident/v                         $ t = v
                  | lpar TypeList/tl rpar           $ t = tuple(tl)
    #              | star ident/f                    $ t = '*' + f
                    ;
    
    TypeList/tl ->  Type/t                          $ tl = [t]
                    (comma Type/t                   $ tl.append(t)
                    )*
                    ;
    """
    



# Name of the root node for this language's hierarchy.
rootname = ''

# Definition of the language root node. This definition is modified
# to substitute the proper root name.
rootdef = \
"""# Root of the language hierarchy.
class {0}(AST):
    pass

"""

def setRootName(name):
    global rootname, rootdef
    rootname = name
    rootdef = rootdef.format(name)

# Header.
header = \
"""# {0} abstract syntax tree node classes.
# Automatically generated from {1}.

from darkitnode import \\
    Symtab, Symbol, AST, \\
    QUANT_NORMAL, QUANT_OPTIONAL, QUANT_LIST, QUANT_NONEMPTY

"""

# These mappings are extended with the user-defined primitives and
# emitted into the output code.
prim_types = \
"""# Mapping from ASDL primitive type names to their PyObject equivalents.
primitive_types = {{
    'identifier':   str,
    'int':          int,
    'string':       str,
    'bool':         bool,
    
    'symtab':       Symtab,
    'sym':          Symbol,
    
    'object':       object{0}}}

"""

# The names of the primitives (extended with the user-defined ones) are
# also used internally by this program.
prim_names = [
    'identifier',
    'int',
    'string',
    'bool',
    
    'symtab',
    'sym',
    
    'object']

# Names of the nodes we've seen defined so far.
node_names = []



class NodeInfo:
    """Store information about a node type and emit the Python code to define it."""
    
    classtemplate = \
"""class {0}({1}):
{2}
"""
    attrline = \
"""    {0} = {1}
"""
    
    quantstr = {'':     'QUANT_NORMAL',
                '?':    'QUANT_OPTIONAL',
                '*':    'QUANT_LIST',
                '+':    'QUANT_NONEMPTY'}
    
    def __init__(self, classname, basename, fields, annstr):
        self.classname = classname
        self.basename = basename
        self.fields = fields
        self.annstr = annstr
        
        self.rett = None
        self.teqs = []
        self.inhtvars = []
        self.ftvars = dict()
    
    def parseAnnStr(self):
        s = ' ; '.join(self.annstr)
        s = s.replace('@', '')
        s = s.replace('\n', '')
        if len(s) == 0:
            return
        
        reader = TypeReader()
        try:
            v = reader(s)
        except tpg.SyntacticError as e:
            raise ASDLError('Syntax error in annotation: \'{0}\''.format(s))
        
        for r in v:
            if r[0] is R_RT:
                self.rett = r[1]
            elif r[0] is R_TE:
                self.teqs.append(r[1])
            elif r[0] is R_IV:
                self.inhtvars = r[1]
            elif r[0] is R_FV:
                self.ftvars[r[1][0]] = r[1][1]
    
    def genFieldsStr(self):
        fstrings = []
        for fname, ftype, fquant in self.fields:
            # Check that field type is known.
            if (ftype not in prim_names and
                ftype not in node_names):
                raise ASDLError('Unknown field type \'{0}\''.format(ftype))
            # Check that the quantifier is valid.
            if fquant not in self.quantstr:
                raise ASDLError('Invalid quantifier \'{0}\''.format(fquant))
            # Check that lists are of node type.
            # (This is an internal limitation of darkitast that may be removed.) 
            if ((fquant == '*' or fquant == '+') and
                ftype in prim_names):
                raise ASDLError('Lists cannot contain primitive types')
            
            # Generate the tuple string describing this field.
            fquantname = self.quantstr[fquant]
            fstring = '(\'{0}\', \'{1}\', {2})'.format(fname, ftype, fquantname)
            fstrings.append(fstring)
        
        # Generate the attribute line defining _fields.
        sep = ',\n' + ' '*15
        flist = '[' + sep.join(fstrings) + ']'
        result = self.attrline.format('_fields', flist)
        
        return result
    
    def genTypesStr(self):
        result = ''
        
        if self.rett:
            result += self.attrline.format('_rettype', repr(self.rett))
        
        if self.teqs:
            teqstrings = [repr(teq) for teq in self.teqs]
            sep = ',\n' + ' '*13
            teqlist = '[' + sep.join(teqstrings) + ']'
            result += self.attrline.format('_teqs', teqlist)
        
        if self.inhtvars:
            result += self.attrline.format('_inhtvars', repr(self.inhtvars))
        
        if self.ftvars:
            ftvstrings = [repr(k) + ': ' + repr(v) for k, v in self.ftvars.items()]
            sep = ',\n' + ' '*15
            ftvlist = '{' + sep.join(ftvstrings) + '}'
            result += self.attrline.format('_ftvars', ftvlist)
        
        return result
    
    def genClassCode(self):
        """Generate class definition containing superclass and field information."""
        
        # Generate _fields.
        fieldsstr = self.genFieldsStr()
        
        # Parse annotations.
        self.parseAnnStr()
        
        tstr = self.genTypesStr()
        
        attrstr = fieldsstr + tstr
        
        return self.classtemplate.format(self.classname, self.basename, attrstr)



def updatePrims(prims):
    """Add entries for user-defined primitive types to both
    prim_types and prim_names."""
    global prim_types, prim_names
    newprim_text = ''
    
    for i, p in enumerate(prims):
        prim_names.append(p)
        
        # Form text to add to prim_types.
        if i == 0:
            newprim_text += ',\n    \n'
        # Unfortunately, '...' screws up Pydev's parsing of the file for
        # autocompetion, so we use the less fancy 'Ellipsis' identifier
        # instead.
        newprim_text += '    {0:<16}'.format('\'{0}\':'.format(p)) + 'Ellipsis'
        if i != len(prims) - 1:
            newprim_text += ',\n'
    
    # Update prim_types.
    prim_types = prim_types.format(newprim_text)

def updateNodes(nodes):
    """Add entries for user-defined node types to node_names."""
    global node_names
    node_names.extend(n.classname for n in nodes)

def genDARkitNodes(asdl):
    """Parse ASDL text and return the corresponding Python code."""
    # Read and parse the input file.
    reader = ASDLReader()
    (language, prims), nodes = reader(asdl)
    
    # Update globals with this information before emitting code.
    updatePrims(prims)
    updateNodes(nodes)
    
    output = ''
    output += header.format(language, grammarfile)
    output += prim_types
    output += rootdef
    output += '\n\n'
    output += ''.join([n.genClassCode() for n in nodes])
    
    return output

if __name__ == '__main__':
    import sys
    
    if len(sys.argv) != 3:
        sys.stderr.write('Usage: {0} <abstract grammar> <output file>'.format(sys.argv[0]))
        sys.exit(1)
    
    grammarfile = sys.argv[1]
    nodesfile = sys.argv[2]
    
    asdl_in = open(grammarfile).read()
    nodes_out = genDARkitNodes(asdl_in)
    f = open(nodesfile, 'wt')
    f.write(nodes_out)
    f.close()
    
    print('Read {0}, wrote {1}.'.format(grammarfile, nodesfile))
    print('Done.')
