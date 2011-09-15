# Unit tests for various things.

import unittest
from darkitast import *
from darhiast import *



class Tests(unittest.TestCase):
    def test_CodeFragment(self):
        # Test fragment:
        # ----------------
        # for i, j in S:
        #     print(i)
        #     print(foo(j))
        #     if i == 0:
        #         print('i is 0')
        #     elif i == 1:
        #         print('i is 1')
        #     else:
        #         pass
        # while x, y in S:
        #     S remove (x, y)
        
        i = VSymbol('i')
        j = VSymbol('j')
        S = VSymbol('S')
        pr = FSymbol('print')
        foo = FSymbol('foo')
        x = VSymbol('x')
        y = VSymbol('y')
        
        n_target = PatTuple([PatVar(i, P_UNBOUND), PatVar(j, P_UNBOUND)])
        n_iter = Name(S)
        n_p1 = CallProc(pr, [Name(i)])
        n_p2 = CallProc(pr, [CallFunc(foo, [Name(j)])])
        n_p3 = CallProc(pr, [Str('i is 0')])
        n_p4 = CallProc(pr, [Str('i is 1')])
        n_if = If([CondCase(BinOp(Name(i), Eq(), Num(0)), Block([n_p3])),
                   CondCase(BinOp(Name(i), Eq(), Num(1)), Block([n_p4]))],
                  Block([Pass()]))
        n_for = For(PatMatch(n_target, n_iter), Block([n_p1, n_p2, n_if]))
        
        n_rem = SetUpdate(S, UpRemove(), Tuple([Name(i), Name(j)]))
        n_match = PatMatch(PatTuple([PatVar(x, P_UNBOUND), PatVar(j, P_UNBOUND)]),
                           Name(S))
        n_patwhile = PatWhile(n_match, Block([n_rem]))
    
    def test_NoFieldError(self):
        node = Pass()
        self.assertRaises(NoFieldError, lambda: node.dne)
    
    def test_FieldAssign(self):
        i = VSymbol('i')
        j = VSymbol('j')
        node = Name(i)
        self.assert_(node.id == i)
        node.id = j
        self.assert_(node.id == j)
    
    def test_FieldTypeError(self):
        node = Name(VSymbol('i'))
        def foo(): node.id = 'j'
        self.assertRaises(FieldTypeError, foo)
    
    def test_FieldListTypeError(self):
        i = VSymbol('i')
        node = If([CondCase(BinOp(Name(i), Eq(), Num(1)), Block([Pass()]))])
        node.cases[:0] = [CondCase(BinOp(Name(i), Eq(), Num(-1)), Block([Pass()]))]
        def foo(): node.cases[:0] = [Pass()]
        self.assertRaises(FieldListTypeError, foo)
    
    def test_NonEmptyError(self):
        i = VSymbol('i')
        node = If([CondCase(BinOp(Name(i), Eq(), Num(1)), Block([Pass()]))])
        def foo(): node.cases[:] = []
        self.assertRaises(NonEmptyError, foo)
    
    def test_FieldListAssignDel(self):
        ca = CallProc(FSymbol('a'), [])
        cb = CallProc(FSymbol('b'), [])
        cc = CallProc(FSymbol('c'), [])
        node = Block([Pass()])
        node.stmtlist[1:] = [ca, cb]
        node.stmtlist[1] = cc
        del node.stmtlist[0]
        self.assert_(len(node.stmtlist) == 2)
        self.assert_(node.stmtlist[0] is cc)
    
    def test_FieldListDuplicationError(self):
        ca = CallProc(FSymbol('a'), [])
        cb = CallProc(FSymbol('b'), [])
        cc = CallProc(FSymbol('c'), [])
        node = Block([ca, cb, cc])
        def foo(): node.stmtlist[0] = node.stmtlist[1]
        self.assertRaises(FieldListDuplicationError, foo)
    
    def test_FieldListSelfAssign(self):
        ca = CallProc(FSymbol('a'), [])
        cb = CallProc(FSymbol('b'), [])
        cc = CallProc(FSymbol('c'), [])
        node = Block([ca, cb, cc])
        node.stmtlist[:] = node.stmtlist[:]
    
    def test_FieldSelfAssign(self):
        ca = CallProc(FSymbol('a'), [])
        cb = CallProc(FSymbol('b'), [])
        cc = CallProc(FSymbol('c'), [])
        node = Block([ca, cb, cc])
        node.stmtlist = node.stmtlist
    
    def test_Validity(self):
        v = VSymbol('v')
        a = Num(1)
        b = Num(2)
        node1 = Assign(PatVar(v, P_UNBOUND), a)
        node2 = Assign(PatVar(v, P_UNBOUND), b)
        node1.value = b
        self.assert_(isvalid(b))
        self.assert_(getParent(a) is nilparent)
        self.assertFalse(isvalid(node2))



dtl = unittest.defaultTestLoader
ts = dtl.loadTestsFromTestCase(Tests)
tr = unittest.TextTestRunner()
tr.run(ts)
