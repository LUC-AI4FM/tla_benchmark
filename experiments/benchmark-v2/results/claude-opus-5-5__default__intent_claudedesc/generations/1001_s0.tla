------------------------------- MODULE Barrier -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES pc, arrived

vars == <<pc, arrived>>

States == {"working", "waiting", "done"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ arrived \subseteq Procs

Init ==
    /\ pc = [p \in Procs |-> "working"]
    /\ arrived = {}

\* Process p reaches the barrier, records its arrival and blocks.
Arrive(p) ==
    /\ pc[p] = "working"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ arrived' = arrived \cup {p}

\* Process p crosses the barrier. This is enabled only once all N
\* processes have arrived.
Cross(p) ==
    /\ pc[p] = "waiting"
    /\ arrived = Procs
    /\ Cardinality(arrived) = N
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED arrived

\* Once every process has crossed, the system terminates. Stuttering
\* is allowed here so that this state does not count as a deadlock.
Terminated ==
    /\ \A p \in Procs : pc[p] = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Arrive(p) \/ Cross(p)
    \/ Terminated

Fairness ==
    \A p \in Procs : WF_vars(Arrive(p)) /\ WF_vars(Cross(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* No premature crossing: if any process has crossed, every process
\* has already arrived and none is still working.
NoPrematureCrossing ==
    \A p \in Procs :
        pc[p] = "done" => (arrived = Procs /\ \A q \in Procs : pc[q] # "working")

\* The arrival set is consistent with the process states.
ArrivedConsistent ==
    \A p \in Procs : (p \in arrived) <=> (pc[p] \in {"waiting", "done"})

\* A waiting process stays blocked while some process has not arrived.
BlockingBehavior ==
    (\E q \in Procs : pc[q] = "working") =>
        \A p \in Procs : pc[p] # "done"

Safety == TypeOK /\ NoPrematureCrossing /\ ArrivedConsistent /\ BlockingBehavior

-----------------------------------------------------------------------------
\* Liveness properties

AllArrived == \A p \in Procs : pc[p] \in {"waiting", "done"}
AllDone    == \A p \in Procs : pc[p] = "done"

\* Progress: if all processes reach the barrier, all eventually proceed.
Progress == AllArrived ~> AllDone

\* No process waits forever once the barrier condition is satisfied.
NoIndefiniteWait ==
    \A p \in Procs : (pc[p] = "waiting" /\ arrived = Procs) ~> (pc[p] = "done")

\* Every process eventually arrives, and eventually all cross.
EventualCompletion == <>AllDone

THEOREM Spec => [](Safety)
THEOREM Spec => Progress /\ NoIndefiniteWait /\ EventualCompletion
=============================================================================