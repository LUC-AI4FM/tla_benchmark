----------------------------- MODULE PowerSubsetTrivial -----------------------------

EXTENDS Integers, Naturals

VARIABLES b

Init == b = TRUE

PowsetConj ==
  /\ (SUBSET (1..3) \subseteq SUBSET (1..5))
  /\ ~(SUBSET (1..5) \subseteq SUBSET (1..3))
  /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
  /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
  /\ (SUBSET Nat \subseteq SUBSET Int)
  /\ ~(SUBSET Int \subseteq SUBSET Nat)

Next == b' = PowsetConj

Spec == Init /\ [] [Next]_b

Inv == (b = TRUE) /\ (b \in BOOLEAN)

================================================================================