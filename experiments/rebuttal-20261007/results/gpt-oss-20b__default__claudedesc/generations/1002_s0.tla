MODULE CyclicBarrier

EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLE pc

(* Type invariant *)
TypeOK == /\ pc \in [1..N -> {"b0","b1"}]

Init == /\ pc = [i \in 1..N |-> "b0"]

b0(self) ==
  /\ self \in 1..N
  /\ pc[self] = "b0"
  /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 ==
  /\ \A i \in 1..N : pc[i] = "b1"
  /\ pc' = [i \in 1..N |-> "b0"]

Next == (∃ self \in 1..N : b0(self)) \/ b1

(* Barrier property: if some process is at b0 and another at b1, the latter stays at b1 in next step *)
BarrierInvariant ==
  ∀ i, j \in 1..N :
    (pc[i] = "b0" /\ pc[j] = "b1") => pc'[j] = "b1"

Spec == Init /\ [][Next]_pc

SafetySpec == Spec /\ []TypeOK /\ [] (Next => BarrierInvariant)

THEOREM SafetySpec