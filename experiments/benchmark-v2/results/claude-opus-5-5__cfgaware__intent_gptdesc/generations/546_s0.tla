------------------------------ MODULE RoundRobinMutex ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1..N

\* pc   : control location of each process
\* cs   : whether each process is currently in its critical section
\* turn : shared token designating which process may enter next
VARIABLES pc, cs, turn

vars == << pc, cs, turn >>

Locations == {"ncs", "try", "crit", "exit"}

NextProc(p) == (p % N) + 1

TypeOK ==
    /\ pc \in [Procs -> Locations]
    /\ cs \in [Procs -> BOOLEAN]
    /\ turn \in Procs

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ cs = [p \in Procs |-> FALSE]
    /\ turn \in Procs

\* Noncritical section: finish noncritical work and start requesting.
NonCritical(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED << cs, turn >>

\* Await permission: enter only when the token designates p.
Enter(p) ==
    /\ pc[p] = "try"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "crit"]
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ UNCHANGED turn

\* Leave the critical section.
Leave(p) ==
    /\ pc[p] = "crit"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ UNCHANGED turn

\* Hand the token deterministically to the next process in cyclic order.
HandOff(p) ==
    /\ pc[p] = "exit"
    /\ turn' = NextProc(p)
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED cs

Proc(p) == NonCritical(p) \/ Enter(p) \/ Leave(p) \/ HandOff(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------
\* Correctness properties

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(cs[p] /\ cs[q])

PcCsConsistent ==
    \A p \in Procs : cs[p] <=> (pc[p] = "crit")

TokenInRange == turn \in Procs

Inv == TypeOK /\ MutualExclusion /\ PcCsConsistent /\ TokenInRange

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "try") ~> (pc[p] = "crit")

EventuallyEnters ==
    \A p \in Procs : []<>(cs[p])

=================================================================================