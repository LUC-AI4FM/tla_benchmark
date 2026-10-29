------------------------------ MODULE AbstractMutexLock ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Procs

ASSUME ProcsAssumption == /\ IsFiniteSet(Procs)
                          /\ Cardinality(Procs) >= 2

VARIABLES lock, pc

vars == << lock, pc >>

LockStates    == {"unlocked", "locked"}
ControlStates == {"ncs", "trying", "cs", "releasing"}

\* A process "holds" the lock while it is in the critical section
\* or in the releasing state (after acquiring, before release completes).
HoldsLock(p) == pc[p] \in {"cs", "releasing"}

Holders == {p \in Procs : HoldsLock(p)}

-----------------------------------------------------------------------------
\* Initial condition

Init == /\ lock = "unlocked"
        /\ pc = [p \in Procs |-> "ncs"]

-----------------------------------------------------------------------------
\* Transitions

\* Leave the non-critical section and start trying to acquire the lock.
Request(p) == /\ pc[p] = "ncs"
              /\ pc' = [pc EXCEPT ![p] = "trying"]
              /\ UNCHANGED lock

\* Acquire the lock. Blocks (is disabled) while the lock is held.
Acquire(p) == /\ pc[p] = "trying"
              /\ lock = "unlocked"
              /\ lock' = "locked"
              /\ pc' = [pc EXCEPT ![p] = "cs"]

\* Finish the critical section and begin releasing the lock.
ExitCS(p) == /\ pc[p] = "cs"
             /\ pc' = [pc EXCEPT ![p] = "releasing"]
             /\ UNCHANGED lock

\* Release the lock and return to the non-critical section.
Release(p) == /\ pc[p] = "releasing"
              /\ lock' = "unlocked"
              /\ pc' = [pc EXCEPT ![p] = "ncs"]

Step(p) == \/ Request(p)
           \/ Acquire(p)
           \/ ExitCS(p)
           \/ Release(p)

Next == \E p \in Procs : Step(p)

-----------------------------------------------------------------------------
\* Fairness: a lock holder always eventually leaves the CS and releases;
\* a trying process repeatedly offered the lock eventually acquires it.
\* Processes are not forced to leave the non-critical section.

Fairness == \A p \in Procs : /\ WF_vars(ExitCS(p))
                             /\ WF_vars(Release(p))
                             /\ SF_vars(Acquire(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety-only specification (no fairness).
SafetySpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK == /\ lock \in LockStates
          /\ pc \in [Procs -> ControlStates]

MutualExclusion == \A p, q \in Procs :
                      (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Stronger: at most one process holds the lock (cs or releasing).
ExclusiveOwnership == \A p, q \in Procs :
                         (HoldsLock(p) /\ HoldsLock(q)) => p = q

LockConsistency == /\ (\E p \in Procs : HoldsLock(p)) => lock = "locked"
                   /\ (\A p \in Procs : ~HoldsLock(p)) => lock = "unlocked"

\* Inductive invariant used to prove mutual exclusion.
Inv == /\ TypeOK
       /\ ExclusiveOwnership
       /\ LockConsistency

-----------------------------------------------------------------------------
\* Liveness properties (optional)

\* Whenever someone is trying, some process eventually enters the CS.
DeadlockFreedom == (\E p \in Procs : pc[p] = "trying")
                       ~> (\E p \in Procs : pc[p] = "cs")

\* Every trying process eventually enters the CS.
StarvationFreedom == \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "cs")

\* Every lock holder eventually releases the lock.
EventualRelease == \A p \in Procs : HoldsLock(p) ~> (pc[p] = "ncs")

-----------------------------------------------------------------------------
\* Proof obligations

THEOREM InitEstablishesInv == Init => Inv
THEOREM InvInductive == Inv /\ [Next]_vars => Inv'
THEOREM SafetyTheorem == SafetySpec => [](TypeOK /\ MutualExclusion /\ LockConsistency)
THEOREM SpecSafety == Spec => [](Inv /\ MutualExclusion)
THEOREM SpecLiveness == Spec => (DeadlockFreedom /\ StarvationFreedom /\ EventualRelease)

=============================================================================