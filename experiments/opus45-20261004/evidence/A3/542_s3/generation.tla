---- MODULE PlusCalIncrement ----

EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

vars == <<x, pc>>

Procs == {ProcA, ProcB}

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "increment"]

IncrementA ==
    /\ pc[ProcA] = "increment"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

IncrementB ==
    /\ pc[ProcB] = "increment"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ IncrementA
    \/ IncrementB
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: x is always non-negative and at most 2
TypeInvariant ==
    /\ x \in 0..2
    /\ pc \in [Procs -> {"increment", "Done"}]

\* Safety invariant: x equals the number of processes that have finished
XCountsDone ==
    x = Cardinality({p \in Procs : pc[p] = "Done"})

\* Liveness property: eventually all processes are done
Termination == <> (\A p \in Procs : pc[p] = "Done")

====