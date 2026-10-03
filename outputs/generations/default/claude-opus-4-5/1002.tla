---------------------------- MODULE SimpleBarrier ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N > 0

VARIABLES pc

Procs == 1..N

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

Spec == Init /\ [][Next]_pc

BarrierProperty == 
    \A p, q \in Procs : 
        (pc[p] = "b0" /\ pc[q] = "b1") => pc'[q] = "b1"

BarrierInvariant ==
    \A p, q \in Procs :
        pc[p] = "b0" => 
            (pc[q] = "b1" => 
                (\A r \in Procs : pc[r] = "b1") = FALSE \/ pc[q] = "b1")

NoPartialReset ==
    \A p, q \in Procs :
        ~(pc[p] = "b0" /\ pc[q] = "b1" /\ 
          (\E r \in Procs : pc[r] = "b0" /\ r # p))

SafeBarrier ==
    [][(\A p \in Procs : pc[p] = "b1") \/ 
       (\A p \in Procs : pc'[p] # "b0" \/ pc[p] = "b0")]_pc

CannotLeaveWhileOthersNotEntered ==
    \A p, q \in Procs :
        (pc[q] = "b0" /\ p # q) => 
            ~(pc[p] = "b1" /\ pc'[p] = "b0" /\ pc'[q] = "b0" /\ pc[q] = "b0")

AllOrNoneReset ==
    [][\A p, q \in Procs : 
        (pc[p] = "b1" /\ pc'[p] = "b0") => 
        (pc[q] = "b1" /\ pc'[q] = "b0")]_pc

=============================================================================