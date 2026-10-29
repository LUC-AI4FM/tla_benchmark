---------------------------- MODULE BoundedStateMachine ----------------------------
EXTENDS Naturals

VARIABLE x

vars == << x >>

\* The prescribed finite domain of natural numbers (bounded numeric type)
Domain == 0..5

\* The unique initial value
InitValue == 0

TypeOK == x \in Domain

Init == x = InitValue

\* Unconditional assignment to a fixed value
SetFixed == x' = InitValue

\* Next value lies in a contiguous subrange
ChooseInRange == x' \in InitValue..InitValue

\* Transitions guarded by specific current-state values
GuardedA == x = 3 /\ x' = 4

GuardedB == x = 4 /\ x' \in 2..3

\* A guarded choice that contradicts the bounded type (target outside Domain)
GuardedOutOfType == x = 5 /\ x' = 9

Next ==
    \/ SetFixed
    \/ ChooseInRange
    \/ GuardedA
    \/ GuardedB
    \/ GuardedOutOfType

Spec == Init /\ [][Next]_vars

\* Global invariant: type-correctness together with preservation of the initial value
Inv == TypeOK /\ x = InitValue

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
=====================================================================================