################################################################################
# main.py: Driver module.                                                      #
# Author: Jon Brandvein                                                        #
################################################################################

import sys
import time
import itertools

import common
import darkitast as dka
import darhiast as dha
import symtab as st
import darkitutils as du
import computils as cu
#import alttag
import pydarkit as pyd
import pair
import inc
import pattern as pat



# Get singleton.
dks = common.dks

dks.DOMAIN = dks.TUPLE_DOMAIN
#dks.DOMAIN = dks.OBJECT_DOMAIN

dks.STRICT = True
#dks.STRICT = False

# Required.
dks.DSET = True
#dks.DSET = False

dks.INCR = True
#dks.INCR = False

# Required.
#dks.INLINE = True
dks.INLINE = False

# Required.
dks.IMPL = True
#dks.IMPL = False

dks.LEAVE_PD = True
#dks.LEAVE_PD = False

dks.REORDER_CLAUSES = True
#dks.REORDER_CLAUSES = False

dks.PRUNE_REFCOUNT_PROPAGATION = True
#dks.PRUNE_REFCOUNT_PROPAGATION = False

#dks.USET = True
dks.USET = False

#dks.TAG = True
dks.TAG = False

dks.ALLPRED = True
#dks.ALLPRED = False



COMPS_ALL = 'ALL'
COMPS_NONE = 'NONE'

class CompNotFound(Exception):
    pass



def printTask(text):
    print(format(text + '... ', '50'), end = '')
    sys.stdout.flush()

def printDone():
    print('Done.')

rebuildTree = du.rebuildTree

def parseArgs(argv):
    
    # Print usage if incorrect.
    if len(argv) != 4:
        sys.stderr.write(
"""Usage: <python 3.1> main.py <infile> <outfile prefix> <comprehensions>
where <comprehensions> = <funcname>:<number>,... | 'ALL' | 'NONE'
example:
    python main.py corerbac.py corerbac_chkacc CheckAccess:1"""
        )
        
        sys.exit(1)
    
    # Get filenames.
    py_inname = argv[1]
    dh_outname = argv[2] + '.dh'
    dl_outname = argv[2] + '.dl'
    pat_outname = argv[2] + '.pt'
    py_outname = argv[2] + '.py'
    
    # Get comprehensions to incrementalize.
    compstr = argv[3]
    
    if compstr.upper() == 'ALL':
        comps = COMPS_ALL
    
    elif compstr.upper() == 'NONE':
        comps = COMPS_NONE
    
    else:
        comps = []
        for compinfo in compstr.split(','):
            comps.append(compinfo)
            
#            locinfo = compinfo
#            
#            func, num = locinfo.split(':')
#            num = int(num)
#            comploc = cu.CompLoc(func, num)
#            complocs.append(comploc)
    
    return (py_inname, dh_outname, dl_outname, pat_outname, py_outname, comps)

def readDARhi(filename):
    """Read the Python input file and return a processed DARhi tree."""
    printTask('Reading ' + filename)
    
    # Get Python AST.
    python_in = open(filename, 'r')
    pysrc = python_in.read()
    python_in.close()
    
    # Convert to DARhi.
    dar_tree = pyd.importPythonToDARhi(pysrc, dks.STRICT, dks.DOMAIN)
    rebuildTree(dar_tree)
    
    printDone()
    
    return dar_tree

def enterPairDomain(tree):
    printTask('Entering pair domain')
    pair.enterPairDomain(tree)
    rebuildTree(tree)
    printDone()

def leavePairDomain(tree):
    printTask('Leaving pair domain')
    pair.leavePairDomain(tree)
    rebuildTree(tree)
    printDone()

def writeDARhi(filename, tree):
    printTask('Writing ' + filename)
    dar_out = open(filename, 'wt')
    dar_out.write(dha.genSyntax(tree))
    dar_out.close()
    printDone()

def writePython(filename, tree):
    printTask('Writing ' + filename)
    py_out = open(filename, 'wt')
    py_out.write(pyd.generatePython(tree))
    py_out.close()
    printDone()



def preprocessComprehensions(tree):
    
#    def locmatch(loc, comploc):
#        # Compare location argument string to internal format.
#        name = loc.cls.id.name if loc.cls is not None else None
#        func = loc.func.id.name if loc.func is not None else None
#        compnum = loc.compnum
#        return (name, func, compnum) == comploc
    
    printTask('Preprocessing comprehensions')
    
    cu.rewriteParams(tree)

def incrementalizeComprehensions(tree, verbose = True):
    if verbose:
        print('Incrementalizing...')
    
    invsyms = st.gatherInvSymbols(tree)
    sys.exit()
    for comp in invsyms:
        if verbose:
            print('  ' + comp.name)
        
        inc.incComp(tree, invsym)
        
        sys.exit()
        
        # Strictify!
#        du.rewriteSetUpdates(tree)
        if dks.PRUNE_REFCOUNT_PROPAGATION:
            du.rewriteMultisets(tree)
        
        rebuildTree(tree)
    
    rebuildTree(tree)

def depatternize1(tree):
    printTask('Depatternizing')
    auxmaskmap = pat.depatternize(tree)
    rebuildTree(tree)
    printDone()
    return auxmaskmap

def depatternize2(tree, auxmaskmap):
    pat.auxmapupdates(tree, auxmaskmap)
    du.eliminateApplCase(tree)



def main():
    
    # Parse arguments.
    args = parseArgs(sys.argv)
    py_inname, dh_outname, dl_outname, pat_outname, py_outname, complocs = args
    
    dar_tree = readDARhi(py_inname)
    
    # Preprocess comprehensions.
    preprocessComprehensions(dar_tree)
    
    # Expand bulk updates.
    du.rewriteBulkUpdates(dar_tree)
    
    # Make set updates strict.
    du.rewriteSetUpdates(dar_tree)
    
    # TODO: rewrite fields
    
    print(dha.genSyntax(dar_tree))
    sys.exit()
    
#    if dks.DOMAIN is dks.OBJECT_DOMAIN:
#        enterPairDomain(dar_tree)
    
#    if dks.TAG:
#        for comp in incrcomps:
#            alttag.tagify(dar_tree, comp)
#        
#        rebuildTree(dar_tree)
#        
#        incrcomps[:0] = [tc.id for c in incrcomps
#                         if hasattr(c.info, 'taginfo')
#                         for tc in c.info.taginfo.tagcomps]
    
#    # The tag comprehensions should be handled *after* the query.
#    # This follows the chain rule, provided we understand tags as
#    # incrementalizable expressions introduced by maintenance code,
#    # rather than as subexpressions of the query.
#    incrcomps.extend(tc.id for c in incrcomps
#                     if hasattr(c.info, 'taginfo')
#                     for tc in c.info.taginfo.tagcomps)
    
    writeDARhi(dl_outname, dar_tree)
    
    # Rewrite wildcards.
    ### TODO: equalcard rewriting as well.
    cu.rewriteWildcards(dar_tree)
    
    # Incrementalize.
    incrementalizeComprehensions(dar_tree)
    
#    writeDARhi(dl_outname, dar_tree)
    
    # Handle wildcards.
    
#    du.WildcardRewriter().run(dar_tree)
#    rebuildTree(dar_tree)
#    
#    wildcomps = cu.liftComprehensions(dar_tree, True, False)
#    rebuildTree(dar_tree)
#    
#    incrementalizeComprehensions(dar_tree, wildcomps, verbose = False)
    
    
    # Split dh tree from patton tree.
    dh_tree = dar_tree
    
    auxmaskmap = depatternize1(dh_tree)
    
    if dks.LEAVE_PD:
#        print(dha.genSyntax(dh_tree))
        leavePairDomain(dh_tree)
    
    depatternize2(dh_tree, auxmaskmap)
    
    # Output DARhi.
    writeDARhi(dh_outname, dh_tree)
    
    # Output Python
#    writePython(py_outname, py_tree)
    writePython(py_outname, dh_tree)
        
    print('Finished!')
    
    
    
    # Here's fun code that crashes my Python interpreter for some reason.
    # Probably it's because darkitnode.FieldLists subclasses str and overrides
    # basic string methods, so the interpreter thinks it's a built-in string
    # and gets a rude surprise.
#    fl = dar_tree.main.stmtlist
#    object() + fl



# Don't take the main name in vain.
if __name__ == '__main__':
    main()
