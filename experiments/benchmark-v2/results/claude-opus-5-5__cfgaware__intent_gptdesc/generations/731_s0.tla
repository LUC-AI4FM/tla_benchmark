---- MODULE BoundedCounter ----
EXTENDS Naturals

CONSTANT UpperBound

ASSUME UpperBound \in Nat /\ UpperBound > 0

VARIABLE counter

vars == << counter >>

TypeOK == counter \in Nat

Init == counter = 0

Increment ==
    /\ counter + 1 < UpperBound
    /\ counter' = counter + 1

Halt ==
    /\ counter + 1 >= UpperBound
    /\ UNCHANGED counter

Next == Increment \/ Halt

Constraint == counter < UpperBound

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

Safety == []Constraint

Progress == \A n \in 0..(UpperBound - 1) : <>(counter >= n)

KeepsIncrementing == [](counter + 1 < UpperBound => <><<Increment>>_vars)

====