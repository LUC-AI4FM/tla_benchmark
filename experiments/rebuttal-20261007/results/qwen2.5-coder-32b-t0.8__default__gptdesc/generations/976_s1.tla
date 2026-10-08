------------------------------- MODULE RingAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

Proc == {p \in 1..N}

Init == 
    /\ x = [p \in Proc |-> 0]
    /\ y = [p \in Proc |-> 0]
    /\ pc = [p \in Proc |-> "init"]

Next ==
    \/ /\ \/ pc["p"] = "init"
          /\ x' = [x EXCEPT ![p] = 1]
          /\ y' = y
          /\ pc' = [pc EXCEPT ![p] = "copy"]
       \/ /\ pc["p"] = "copy"
          /\ LET left \equiv IF p = 1 THEN N ELSE p - 1
          IN x' = x
             /\ y' = [y EXCEPT ![p] = x[left]]
             /\ pc' = [pc EXCEPT ![p] = "done"]
    \/ pc["p"] = "done"
       /\ UNCHANGED <<x, y>>
       /\ pc' = pc

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, pc>>

Inv ==
    /\ \A p \in Proc : pc[p] \in {"init", "copy", "done"}
    /\ (\E p \in Proc : pc[p] = "done") => (\E q \in Proc : y[q] = 1)

TypeOK ==
    /\ x \in [Proc -> {0, 1}]
    /\ y \in [Proc -> {0, 1}]
    /\ pc \in [Proc -> {"init", "copy", "done"}]

Safety == [](Inv)

Liveness == <>(\A p \in Proc : pc[p] = "done")

Theorem ==
    Spec => []TypeOK /\ Safety /\ Liveness
=============================================================================