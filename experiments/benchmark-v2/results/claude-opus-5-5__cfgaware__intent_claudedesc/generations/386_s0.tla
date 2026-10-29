---- MODULE ModuleInstantiation ----
EXTENDS Naturals

CONSTANT D

ASSUME D + 0 = 42

---- MODULE Inner ----
CONSTANTS X, Y

InnerVal == X

InnerZero == Y

InnerPair == <<X, Y>>
====