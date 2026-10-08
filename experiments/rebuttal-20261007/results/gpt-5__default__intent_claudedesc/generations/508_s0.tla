------------------------------ MODULE SquareAssertion ------------------------------

EXTENDS Naturals, TLC

CONSTANT defaultInitValue

(*
--algorithm Check
variables x \in 1..10;
variables done = FALSE;
begin
A:
  assert x * x <= 100;
B:
  done := TRUE;
end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES x, done, pc

vars == << x, done, pc >>

Init ==
  /\ x \in 1..10
  /\ done = FALSE
  /\ pc = "A"

A ==
  /\ pc = "A"
  /\ Assert(x * x <= 100, "Square within bound")
  /\ pc' = "B"
  /\ UNCHANGED << x, done >>

B ==
  /\ pc = "B"
  /\ done' = TRUE
  /\ pc' = "Done"
  /\ UNCHANGED x

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == A \/ B \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

\* Safety invariants
TypeOK ==
  /\ x \in 1..10
  /\ done \in BOOLEAN
  /\ pc \in {"A", "B", "Done"}

SquareOK == x * x <= 100

\* Liveness: the system always terminates (reaches the done state)
Termination == <> (pc = "Done")
\* END TRANSLATION

================================================================================