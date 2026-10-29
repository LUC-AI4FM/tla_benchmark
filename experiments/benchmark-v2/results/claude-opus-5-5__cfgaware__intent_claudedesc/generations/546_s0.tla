---------------------------- MODULE RoundRobinMutex ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES pc, turn

vars == << pc, turn >>

\* Set of processes currently in the critical section
cs == { p \in Procs : pc[p] = "cs" }

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs", "exit"}]
    /\ turn \in Procs

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ turn \in Procs

\* Non-critical section: process decides to try to enter
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED turn

\* Waiting: may enter only when it is this process's turn
Enter(p) ==
    /\ pc[p] = "wait"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

\* Critical section: finish work and move to exit
CritSec(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED turn

\* Exit: hand the turn to the next process in circular order
Exit(p) ==
    /\ pc[p] = "exit"
    /\ turn' = (p + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

proc(p) == NCS(p) \/ Enter(p) \/ CritSec(p) \/ Exit(p)

Next == \E p \in Procs : proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(proc(p))

\* Safety: at most one process in the critical section
MutualExclusion == Cardinality(cs) <= 1

MutualExclusionAlt ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: every waiting process eventually enters the critical section
\* (holds when all processes participate under weak fairness)
Starvation == \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

\* Every process eventually gets the turn
TurnProgress == \A p \in Procs : []<>(turn = p)

=============================================================================