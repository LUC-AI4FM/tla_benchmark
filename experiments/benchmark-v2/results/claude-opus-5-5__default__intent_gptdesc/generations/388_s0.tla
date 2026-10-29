---- MODULE CyclicCounter ----
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE x

vars == <<x>>

Init == x = 0

Increment == x' = (x + 1) % N

Next == Increment

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariants
TypeOK == x \in Nat

InRange == x \in 0..(N - 1)

Inv == TypeOK /\ InRange

\* The step relation preserves the invariant (inductive invariance)
InvPreserved == Inv /\ Next => Inv'

THEOREM InitEstablishesInv == Init => Inv
THEOREM StepPreservesInv == Inv /\ [Next]_vars => Inv'
THEOREM SpecSafety == Spec => []Inv

\* No deadlock: a transition is always enabled
AlwaysEnabled == ENABLED Next

NoDeadlock == []AlwaysEnabled

\* Liveness: transitions continue forever (infinite behavior)
InfinitelyOftenSteps == []<><<Next>>_vars \/ (N = 1)

\* With N > 1, the counter keeps cycling and returns to zero infinitely often
CyclesForever == (N > 1) => []<>(x = 0) /\ []<>(x # 0)

THEOREM SpecNoDeadlock == Spec => NoDeadlock
THEOREM SpecLiveness == Spec => []<>(x = 0)
====