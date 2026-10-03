------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS Naturals, TLC

CONSTANT RM

VARIABLE r2

State == {"working","prepared","committed","aborted"}

Prepare(r) ==
  /\ r ∈ RM
  /\ r2[r] = "working"
  /\ r2' = [r2 EXCEPT ![r] = "prepared"]

Decide(r, d) ==
  /\ r ∈ RM
  /\ d ∈ {"committed","aborted"}
  /\ r2[r] = "prepared"
  /\ r2' = [r2 EXCEPT ![r] = d]

Next == ∃ r ∈ RM :
          (Prepare(r)) \/
          (∃ d ∈ {"committed","aborted"} : Decide(r,d))

Init == ∀ r ∈ RM : r2[r] = "working"

TCSpec == Init /\ [][Next]_r2

TCTypeOK == ∀ r ∈ RM : r2[r] ∈ State

TCConsistent ==
  ¬∃ r1, r2_ ∈ RM :
    (r2[r1] = "committed" /\ r2[r2_] = "aborted")

=============================================================================