---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Naturals

CONSTANTS Procs

ASSUME ProcsAssumption == Procs # {} /\ IsFiniteSet(Procs)

VARIABLES lock, pc

vars == <<lock, pc>>

LockStates == {"unlocked", "locked"}
PCStates == {"noncritical", "trying", "critical", "releasing"}

TypeOK ==
    /\ lock \in LockStates
    /\ pc \in [Procs -> PCStates]

LockInv ==
    /\ (\E p \in Procs : pc[p] \in {"critical", "releasing"}) => lock = "locked"
    /\ (\A p \in Procs : pc[p] \in {"noncritical", "trying"}) => lock = "unlocked"

MutualExclusion ==
    \A p1, p2 \in Procs : (pc[p1] = "critical" /\ pc[p2] = "critical") => p1 = p2

Init ==
    /\ lock = "unlocked"
    /\ pc = [p \in Procs |-> "noncritical"]

EnterTrying(p) ==
    /\ pc[p] = "noncritical"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ lock' = lock

AcquireLock(p) ==
    /\ pc[p] = "trying"
    /\ lock = "unlocked"
    /\ lock' = "locked"
    /\ pc' = [pc EXCEPT ![p] = "critical"]

EnterReleasing(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "releasing"]
    /\ lock' = lock

ReleaseLock(p) ==
    /\ pc[p] = "releasing"
    /\ lock' = "unlocked"
    /\ pc' = [pc EXCEPT ![p] = "noncritical"]

Next ==
    \E p \in Procs :
        \/ EnterTrying(p)
        \/ AcquireLock(p)
        \/ EnterReleasing(p)
        \/ ReleaseLock(p)

Spec == Init /\ [][Next]_vars

SafetyInvariant == TypeOK /\ MutualExclusion /\ LockInv

THEOREM Spec => []SafetyInvariant

IsFiniteSet(S) == \A T \in SUBSET S : T = S \/ T # S

================================================================================