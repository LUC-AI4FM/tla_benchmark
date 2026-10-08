----------------------------- MODULE TwoPhaseCommit -----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS RMs  \* Set of resource managers

VARIABLES states \* States of each RM: "working", "prepared", "committed", "aborted"

Init == 
  /\ states \in [RMs -> {"working"}]

Prepare(r) ==
  /\ states[r] = "working"
  /\ \/ states' = [states EXCEPT ![r] = "prepared"]
     \/ states' = [states EXCEPT ![r] = "aborted"]

Decide(commit, r) == 
  /\ states[r] \in {"working", "prepared"}
  /\ commit \in {TRUE, FALSE}
  /\ IF commit THEN
       states' = [states EXCEPT ![r] = "committed"]
     ELSE
       states' = [states EXCEPT ![r] = "aborted"]

Next ==
  \/ \E r \in RMs : Prepare(r)
  \/ \E r \in RMs, commit \in {TRUE, FALSE} : Decide(commit, r)

Spec == 
  /\ Init
  /\ [][Next]_<<states>>
  /\ WF_next(<<states>>)

TypeOK ==
  /\ states \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Consistency ==
  LET committed = {r \in RMs : states[r] = "committed"}
      aborted = {r \in RMs : states[r] = "aborted"}
  IN
    committed /\ aborted = {}

Invariant == TypeOK /\ Consistency

=============================================================================