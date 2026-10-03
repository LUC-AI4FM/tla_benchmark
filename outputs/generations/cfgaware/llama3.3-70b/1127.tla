---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Integers, TLC

CONSTANT RM

VARIABLE r, r2

TypeOK == (r \in [RM -> {"working", "prepared", "committed", "aborted"}])

TCTypeOK == TypeOK

Prepare(rm) == 
  /\ r[rm] = "working"
  /\ r' = [r EXCEPT ![rm] = "prepared"]
  /\ UNCHANGED << >>

Decide(rm, d) == 
  /\ (r[rm] = "prepared")
  /\ d \in {"commit", "abort"}
  /\ r' = [r EXCEPT ![rm] = IF d = "commit" THEN "committed" ELSE "aborted"]
  /\ UNCHANGED << >>

Next == \E rm \in RM : Prepare(rm) \/ (\E d \in {"commit", "abort"} : Decide(rm, d))

TCConsistent == 
  \A rm1, rm2 \in RM : 
    ~(r[rm1] = "committed" /\ r[rm2] = "aborted")

TCSpec == 
  /\ TypeOK
  /\ [][Next]_<< >>
  /\ WF_vars(Next, << >>)
  /\ TCConsistent

THEOREM TCSpec => []TCConsistent
=============================================================================