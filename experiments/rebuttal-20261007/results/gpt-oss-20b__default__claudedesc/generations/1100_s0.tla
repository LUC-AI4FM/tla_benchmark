------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS Naturals, TLC

Process == {1, 2}
LabelSet == {"l0", "l1", "cs", "l2"}

VARIABLE lock, pc

Init ==
  /\ lock = 1
  /\ pc \in [Process -> LabelSet]
  /\ \A i \in Process : pc[i] = "l0"

L0(i) ==
  /\ pc[i] = "l0"
  /\ pc' = [pc EXCEPT ![i] = "l1"]
  /\ lock' = lock

L1(i) ==
  /\ pc[i] = "l1"
  /\ lock = 1
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![i] = "cs"]

CS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "l2"]
  /\ lock' = lock

L2(i) ==
  /\ pc[i] = "l2"
  /\ lock' = 1
  /\ pc' = [pc EXCEPT ![i] = "l0"]

Next == \E i \in Process : L0(i) \/ L1(i) \/ CS(i) \/ L2(i)

Spec == Init /\ [][Next]_{<<lock, pc>>}

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [Process -> LabelSet]

LockInv ==
  /\ \A i, j \in Process :
        (i # j) => ~(pc[i] \in {"cs", "l2"} /\ pc[j] \in {"cs", "l2"})
  /\ \A i \in Process : (pc[i] \in {"cs", "l2"}) => lock = 0

THEOREM SpecImpliesTypeOK : Spec => [] TypeOK
  PROOF
    OBVIOUS
  END.

THEOREM SpecImpliesLockInv : Spec => [] LockInv
  PROOF
    OBVIOUS
  END.
=============================================================================