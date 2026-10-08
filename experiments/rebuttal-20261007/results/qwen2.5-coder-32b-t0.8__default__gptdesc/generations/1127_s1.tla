------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS RMs  \* Set of Resource Managers

VARIABLES rmStates  \* State of each RM: working, prepared, committed, aborted

Init == 
  /\ rmStates \in [RMs -> {"working"}]
  
Prepare(rm) ==
  /\ rm \in RMs
  /\ rmStates[rm] = "working"
  /\ rmStates' = [rmStates EXCEPT ![rm] = "prepared"]
  
Commit(rm) ==
  /\ rm \in RMs
  /\ rmStates[rm] = "prepared"
  /\ rmStates' = [rmStates EXCEPT ![rm] = "committed"]
  
Abort(rm) ==
  /\ rm \in RMs
  /\ (rmStates[rm] = "working" \/ rmStates[rm] = "prepared")
  /\ rmStates' = [rmStates EXCEPT ![rm] = "aborted"]

Next ==
  \E rm \in RMs : Prepare(rm) \/ Commit(rm) \/ Abort(rm)

Spec == 
  /\ Init
  /\ [][Next]_<<rmStates>>
  
Invariant1 == \A r1, r2 \in RMs: NOT (rmStates[r1] = "committed" /\ rmStates[r2] = "aborted")
Invariant2 == \A r1, r2 \in RMs: NOT (rmStates[r1] = "aborted" /\ rmStates[r2] = "committed")

TypeOK ==
  /\ rmStates \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Spec == Spec /\ []TypeOK /\ []Invariant1 /\ []Invariant2

=============================================================================