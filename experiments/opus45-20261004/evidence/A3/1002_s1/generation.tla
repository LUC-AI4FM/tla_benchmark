-------------------------------- MODULE Barrier --------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES pc

vars == <<pc>>

TypeOK == pc \in [Procs -> {"b0", "b1"}]

Init == pc = [p \in Procs |-> "b0"]

Enter(p) == 
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

Reset == 
    /\ \A p \in Procs : pc[p] = "b1"
    /\ pc' = [p \in Procs |-> "b0"]

Next == 
    \/ \E p \in Procs : Enter(p)
    \/ Reset

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AllAtB1 == \A p \in Procs : pc[p] = "b1"

SomeNotEntered == \E p \in Procs : pc[p] = "b0"

BarrierProperty == 
    \A p \in Procs : 
        (pc[p] = "b1" /\ SomeNotEntered) => [][pc[p] = "b1" \/ AllAtB1]_vars

SafetyInvariant == 
    \A p, q \in Procs : 
        (pc[p] = "b0" /\ pc[q] = "b1") => 
            (pc'[q] = "b1" \/ (\A r \in Procs : pc[r] = "b1"))

NoPartialReset == 
    [][\A p \in Procs : 
        (pc[p] = "b1" /\ pc'[p] = "b0") => 
            (\A q \in Procs : pc[q] = "b1")]_vars

EventualReset == 
    \A p \in Procs : pc[p] = "b1" ~> pc[p] = "b0"

================================================================================