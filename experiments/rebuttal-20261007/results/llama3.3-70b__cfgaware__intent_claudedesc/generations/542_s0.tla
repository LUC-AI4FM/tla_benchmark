---------------------------- MODULE SimpleIncrement ----------------------------
EXTENDS Integers

VARIABLE x, p1_done, p2_done

Init == (x = 0) ∧ (p1_done = FALSE) ∧ (p2_done = FALSE)

P1Increment == (x' = x + 1) ∧ (p1_done' = TRUE) ∧ (p2_done' = p2_done)
P2Increment == (x' = x + 1) ∧ (p2_done' = TRUE) ∧ (p1_done' = p1_done)

Next == (∃ t ∈ {1, 2} : 
          IF t = 1 THEN P1Increment ELSE P2Increment)

Spec == Init ∧ [][Next]_<<x, p1_done, p2_done>>
=============================================================================