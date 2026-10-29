---- MODULE Barrier ----
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 1..N

VARIABLE pc

vars == << pc >>

\* "b0" : approaching the barrier (pre-arrival state)
\* "b1" : arrived at the barrier, waiting for release

TypeOK == pc \in [Procs -> {"b0", "b1"}]

Init == pc = [p \in Procs |-> "b0"]

\* A process signals that it has arrived at the barrier
Arrive(p) ==
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

\* Atomic reset: all processes are released together once every process has arrived
Release ==
    /\ \A p \in Procs : pc[p] = "b1"
    /\ pc' = [p \in Procs |-> "b0"]

Next == \/ \E p \in Procs : Arrive(p)
        \/ Release

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: no process leaves the barrier while some process has not yet arrived
BarrierProperty ==
    [][ \A p \in Procs :
          (pc[p] = "b1" /\ pc'[p] = "b0") => (\A q \in Procs : pc[q] = "b1")
      ]_vars

\* Liveness: every process repeatedly reaches the barrier and is released
Progress == \A p \in Procs : []<>(pc[p] = "b1") /\ []<>(pc[p] = "b0")

THEOREM Spec => []TypeOK /\ BarrierProperty

====