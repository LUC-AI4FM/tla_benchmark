--------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Naturals

CONSTANTS RMs

VARIABLE state

(* State values *)
Working   == "Working"
Prepared  == "Prepared"
Committed == "Committed"
Aborted   == "Aborted"

States == {Working, Prepared, Committed, Aborted}

TypeInv == state \in [RMs -> States]

Prepare(r) ==
  /\ r \in RMs
  /\ state[r] = Working
  /\ state' = [state EXCEPT ![r] = Prepared]

DecideCommit(r) ==
  /\ r \in RMs
  /\ state[r] = Prepared
  /\ state' = [state EXCEPT ![r] = Committed]

DecideAbort(r) ==
  /\ r \in RMs
  /\ state[r] = Prepared
  /\ state' = [state EXCEPT ![r] = Aborted]

Next == 
  ∃ r ∈ RMs :
    (Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r))

Init ==
  \A r ∈ RMs : state[r] = Working

ConsistentInv == ¬∃ r1, r2 ∈ RMs : state[r1] = Committed /\ state[r2] = Aborted

Spec == Init /\ [][Next]_state

=============================================================================