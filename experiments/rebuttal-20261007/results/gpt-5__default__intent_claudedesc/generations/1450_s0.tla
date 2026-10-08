------------------------------ MODULE RandomSubsetFunctionSampler ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS SAMPLE_SZ

ASSUME SAMPLE_SZ = 1000

VARIABLES sample

Domain    == 0..8
Codomain  == 0..9
FuncSpace == [Domain -> Codomain]

Init == sample = TLC!RandomSubset(FuncSpace, SAMPLE_SZ)

Next == UNCHANGED sample

vars == << sample >>

Spec == Init /\ [][Next]_vars

TrivialInv == TRUE

===============================================================================