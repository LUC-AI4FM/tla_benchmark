---- MODULE AbstractMutex ----
EXTENDS Naturals

CONSTANT Proc

ASSUME \E p \in Proc : \E q \in Proc : p # q

VARIABLES lock, pc

LockStates == {"Unlocked", "Locked"}
PCStates == {"ncs", "try", "cs", "rel"}

vars == << lock, pc >>

Init ==
  /\ lock = "Unlocked"
  /\ pc = [p \in Proc |-> "ncs"]

NcsToTry(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED lock

TryAcquire(p) ==
  /\ p \in Proc
  /\ pc[p] = "try"
  /\ lock = "Unlocked"
  /\ lock' = "Locked"
  /\ pc' = [pc EXCEPT ![p] = "cs"]

CsToRel(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "rel"]
  /\ UNCHANGED lock

Release(p) ==
  /\ p \in Proc
  /\ pc[p] = "rel"
  /\ lock = "Locked"
  /\ lock' = "Unlocked"
  /\ pc' = [pc EXCEPT ![p] = "ncs"]

PStep(p) == NcsToTry(p) \/ TryAcquire(p) \/ CsToRel(p) \/ Release(p)

Next == \E p \in Proc : PStep(p)

Holding(p) == pc[p] \in {"cs", "rel"}

AnyHolding == \E p \in Proc : Holding(p)

TypeInv ==
  /\ lock \in LockStates
  /\ pc \in [Proc -> PCStates]

MutualExclusion ==
  \A p \in Proc : \A q \in Proc : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

LockConsistency == (AnyHolding <=> lock = "Locked")

Spec == Init /\ [][Next]_vars

SafetyInvariant == TypeInv /\ MutualExclusion /\ LockConsistency

THEOREM Spec => []TypeInv /\ []MutualExclusion /\ []LockConsistency

====