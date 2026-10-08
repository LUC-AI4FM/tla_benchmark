---------------------------- MODULE RandomFunctionSample ----------------------------
EXTENDS Integers, FiniteSets, Randomization

CONSTANTS DomainSize, CodomainSize, SampleSize

ASSUME DomainSize \in Nat /\ DomainSize > 0
ASSUME CodomainSize \in Nat /\ CodomainSize > 0
ASSUME SampleSize \in Nat /\ SampleSize > 0

Domain == 1..DomainSize
Codomain == 1..CodomainSize

FunctionSpace == [Domain -> Codomain]

VARIABLES sampledFunctions

vars == <<sampledFunctions>>

Init == sampledFunctions = RandomSubset(SampleSize, FunctionSpace)

Next == UNCHANGED sampledFunctions

Spec == Init /\ [][Next]_vars

TypeInvariant == sampledFunctions \subseteq FunctionSpace

TrivialInvariant == TRUE

===================================================================================