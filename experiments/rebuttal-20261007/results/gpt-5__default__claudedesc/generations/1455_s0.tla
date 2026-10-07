----------------------------- MODULE SubsetPowerSetRegressionTest -----------------------------

EXTENDS Naturals, Integers

CONSTANTS DummyConstant

VARIABLES b

A1 == (SUBSET (1..23)) \subseteq (SUBSET (1..42))
A2 == ~(SUBSET (1..42) \subseteq SUBSET (1..23))
A3 == (SUBSET (2..42)) \subseteq (SUBSET (1..42))
A4 == ~(SUBSET (1..42) \subseteq SUBSET (2..42))
A5 == (SUBSET {1, 2, 3}) \subseteq (SUBSET {1, 2, 3, 4})
A6 == (SUBSET {}) \subseteq (SUBSET {})
A7 == (SUBSET {}) \subseteq (SUBSET {1})
A8 == ~(SUBSET {1} \subseteq SUBSET {})
A9 == (SUBSET {1}) \subseteq (SUBSET Int)
A10 == (SUBSET {1}) \subseteq (SUBSET Nat)

AllAssertions == A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10

Init == b = TRUE

Next == b' = AllAssertions

Inv == /\ b = TRUE
       /\ b \in BOOLEAN

Spec == Init /\ [][Next]_b

=============================================================================