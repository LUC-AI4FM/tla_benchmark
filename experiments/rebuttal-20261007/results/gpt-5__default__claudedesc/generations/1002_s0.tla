--------------------------- MODULE CyclicBarrier ---------------------------

EXTENDS Integers

(*
  Cyclic barrier synchronization for N processes with two locations: "b0" and "b1".
  N is fixed to 6 as per the description.
*)

N == 6
Proc == 1..N
Locations == {"b0", "b1"}

VARIABLES pc

vars == << pc >>

Init ==
  pc = [p \in Proc |-> "b0"]

AllAtB1 ==
  \A p \in Proc: pc[p] = "b1"

b0(self) ==
  /\ self \in Proc
  /\ pc[self] = "b0"
  /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 ==
  /\ AllAtB1
  /\ pc' = [p \in Proc |-> "b0"]

Next ==
  (\E self \in Proc: b0(self)) \/ b1

Spec ==
  Init /\ [][Next]_vars

(*
  Safety invariant: pc always maps each process to one of the two valid locations.
*)
TypeOK ==
  pc \in [Proc -> Locations]

(*
  Barrier safety step property:
  If some process is still at "b0" and another is at "b1",
  then the latter must remain at "b1" in the next step.
*)
BarrierStep ==
  \A i \in Proc: \A j \in Proc:
    (pc[i] = "b0" /\ pc[j] = "b1") => pc'[j] = "b1"

BarrierProperty ==
  []BarrierStep

=============================================================================