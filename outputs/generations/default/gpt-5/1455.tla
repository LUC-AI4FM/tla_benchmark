----------------------------- MODULE SubsetPowerSetSpec -----------------------------

EXTENDS Naturals, Integers

CONSTANTS Dummy

VARIABLES b

RangePos == (SUBSET (1..3)) \subseteq (SUBSET (1..4))
RangeNeg == ~((SUBSET (1..4)) \subseteq (SUBSET (1..3)))
EnumPos  == (SUBSET {1,2}) \subseteq (SUBSET {1,2,3})
EnumNeg  == ~((SUBSET {1,3}) \subseteq (SUBSET {1,2}))
EnumEq   == (SUBSET {2,4}) \subseteq (SUBSET {2,4})
EmptyNeg == ~((SUBSET {1}) \subseteq (SUBSET {}))
NatIntPos == (SUBSET Nat) \subseteq (SUBSET Int)
NatIntNeg == ~((SUBSET Int) \subseteq (SUBSET Nat))

Assertions ==
  RangePos
  /\ RangeNeg
  /\ EnumPos
  /\ EnumNeg
  /\ EnumEq
  /\ EmptyNeg
  /\ NatIntPos
  /\ NatIntNeg

Init == b = TRUE

Next == b' = Assertions

Spec == Init /\ [] [Next]_b

Invariant == b \in BOOLEAN /\ b = TRUE
AlwaysInvariant == [](b \in BOOLEAN /\ b = TRUE)

=============================================================================