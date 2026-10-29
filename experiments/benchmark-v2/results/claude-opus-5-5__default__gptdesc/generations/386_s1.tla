---------------------------- MODULE test216 ----------------------------
EXTENDS Naturals

CONSTANT D

ASSUME D + 0 = 42

THEOREM D + 0 = 42

Helper == D + 0 = 42

---------------------------- MODULE test216b ----------------------------
CONSTANTS E, y

InnerSum == E + y

InnerFact == E + y = 42
=========================================================================