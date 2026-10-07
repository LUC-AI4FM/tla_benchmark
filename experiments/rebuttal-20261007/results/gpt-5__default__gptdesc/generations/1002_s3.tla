---- MODULE ReusableBarrier ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES pc

Proc == 1..N

States == {"b0", "b1"}

Init ==
  pc = [p \in Proc |-> "b0"]

Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "b0"
  /\ pc' = [pc EXCEPT ![i] = "b1"]

Reset ==
  /\ \A p \in Proc: pc[p] = "b1"
  /\ pc' = [p \in Proc |-> "b0"]

Next ==
  \/ \E i \in Proc: Enter(i)
  \/ Reset

Spec ==
  Init /\ [][Next]_pc

(*
  Safety invariant: the program counter is always a total function
  from Proc to the control states {"b0","b1"}.
*)
TypeOK ==
  pc \in [Proc -> States]

Safety ==
  []TypeOK

(*
  Temporal barrier property:
  No process can leave the barrier (transition b1 -> b0) in a step
  while some other process has not yet entered it (i.e., before all
  are in b1 in the pre-state).
*)
LeaveOccurs ==
  \E i \in Proc: pc[i] = "b1" /\ pc'[i] = "b0"

BarrierProperty ==
  [](LeaveOccurs => \A j \in Proc: pc[j] = "b1")

====