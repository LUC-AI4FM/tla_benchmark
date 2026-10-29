---------------------------- MODULE Countdown ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLE counter

vars == <<counter>>

TypeOK == counter \in 0..N

Init == counter = N

Decrement ==
    /\ counter > 0
    /\ counter' = counter - 1

Done ==
    /\ counter = 0
    /\ UNCHANGED counter

Next == Decrement \/ Done

Spec == Init /\ [][Next]_vars

NonNegative == counter >= 0

Safety == [](counter >= 0)

THEOREM Spec => []NonNegative
=============================================================================