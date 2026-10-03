------------------------------ MODULE TwoState ------------------------------
EXTENDS Naturals, Sequences, TemporalConstants

CONSTANTS Done, MaxHistory

VARIABLES pc, history

(* Set of state variables *)
vars == {pc, history}

Init ==
  /\ pc = "A"
  /\ history = <<>>

A ==
  /\ pc = "A"
  /\ pc' = "B"
  /\ history' = Append(history, pc)

B ==
  /\ pc = "B"
  /\ pc' = "A"
  /\ UNCHANGED history

Next == (A \/ B) \/ UNCHANGED vars

HistoryConstraint == Len(history) <= MaxHistory

Liveness == <> (pc = Done)

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars[A \/ B]
  /\ HistoryConstraint
  /\ Liveness

=============================================================================