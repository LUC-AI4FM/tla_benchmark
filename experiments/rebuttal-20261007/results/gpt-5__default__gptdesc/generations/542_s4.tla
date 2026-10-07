------------------------------ MODULE PlusCalTwoProcs ------------------------------

EXTENDS Naturals

CONSTANTS Proc

ASSUME Proc = {"ProcA", "ProcB"}

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = [p \in Proc |-> "inc"]

Inc(p) ==
  /\ p \in Proc
  /\ pc[p] = "inc"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminated ==
  \A p \in Proc: pc[p] = "Done"

Terminating ==
  /\ Terminated
  /\ UNCHANGED vars

Next ==
  \/ (\E p \in Proc: Inc(p))
  \/ Terminating

Spec ==
  Init /\ [][Next]_vars

(*
  Safety invariants
*)
TypeOK ==
  /\ x \in Nat
  /\ pc \in [Proc -> {"inc", "Done"}]

BoundedX ==
  x <= 2

THEOREM Spec => []TypeOK
THEOREM Spec => []BoundedX
THEOREM Spec => [](Terminated => x = 2)

(*
  Liveness: eventually all processes are done
*)
Termination ==
  <>Terminated

=============================================================================