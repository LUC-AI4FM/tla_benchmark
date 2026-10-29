------------------------------- MODULE AbstractLock -------------------------------
EXTENDS Naturals, FiniteSets

\* Fixed small set of concurrent processes (at least two).
Procs == 1..3

ASSUME Cardinality(Procs) >= 2

VARIABLES lock, pc

vars == <<lock, pc>>

LockStates    == {"unlocked", "locked"}
ControlStates == {"ncs", "trying", "cs", "releasing"}

\* Processes that currently hold the lock (acquired, not yet released)
Holders == {p \in Procs : pc[p] \in {"cs", "releasing"}}

-----------------------------------------------------------------------------------
\* Initial condition: lock unlocked, all processes non-critical.
Init ==
    /\ lock = "unlocked"
    /\ pc = [p \in Procs |-> "ncs"]

\* Leave the non-critical section and begin trying to acquire the lock.
Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ UNCHANGED lock

\* Acquire: enabled only when the lock is free (blocks otherwise).
Acquire(p) ==
    /\ pc[p] = "trying"
    /\ lock = "unlocked"
    /\ lock' = "locked"
    /\ pc' = [pc EXCEPT ![p] = "cs"]

\* Finish the critical section, moving to the releasing state.
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "releasing"]
    /\ UNCHANGED lock

\* Release the lock and return to the non-critical section.
Release(p) ==
    /\ pc[p] = "releasing"
    /\ lock = "locked"
    /\ lock' = "unlocked"
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == Try(p) \/ Acquire(p) \/ ExitCS(p) \/ Release(p)

Next == \E p \in Procs : Proc(p)

\* Weak fairness per process: holders eventually make progress; does not affect safety.
Fairness == \A p \in Procs : WF_vars(ExitCS(p)) /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------
\* Type and state invariant
TypeOK ==
    /\ lock \in LockStates
    /\ pc \in [Procs -> ControlStates]

\* Mutual exclusion
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Lock consistency: at most one holder, and lock is locked iff someone holds it.
LockInv ==
    /\ \A p, q \in Holders : p = q
    /\ (lock = "locked") <=> (Holders # {})
    /\ (lock = "unlocked") <=> (Holders = {})

\* Inductive invariant used to verify mutual exclusion
IndInv == TypeOK /\ LockInv

THEOREM Spec => [](TypeOK /\ LockInv /\ MutualExclusion)
===================================================================================