---------------------------- MODULE ConcurrentIncrement ----------------------------
EXTENDS Integers

CONSTANTS P1, P2

VARIABLES counter, pc

Procs == {P1, P2}

TypeOK == /\ counter \in Int
          /\ pc \in [Procs -> {"ready", "done"}]

Init == /\ counter = 0
        /\ pc = [p \in Procs |-> "ready"]

Increment(p) == /\ pc[p] = "ready"
                /\ counter' = counter + 1
                /\ pc' = [pc EXCEPT ![p] = "done"]

Next == \E p \in Procs : Increment(p)

Fairness == \A p \in Procs : WF_<<counter, pc>>(Increment(p))

Spec == Init /\ [][Next]_<<counter, pc>> /\ Fairness

Termination == <>(pc[P1] = "done" /\ pc[P2] = "done")

AllDone == \A p \in Procs : pc[p] = "done"

TerminationLiveness == <>AllDone

FinalValue == [](AllDone => counter = 2)

===================================================================================