----------------------------- MODULE SubsetOfPowersetSpec -----------------------------

EXTENDS Naturals, Integers

CONSTANTS Dummy

VARIABLES ok

RangeSmall == 1..3
RangeLarge == 1..4
RangeMinusOne == RangeLarge \ {2}

SetX == {1}
SetY == {1, 2}
SetZ == {1, 2, 3}

Empty == {}
Singleton == {0}

Init ==
  /\ ok =
      /\ SUBSET RangeSmall \subseteq SUBSET RangeLarge
      /\ ~(SUBSET RangeLarge \subseteq SUBSET RangeSmall)
      /\ SUBSET RangeMinusOne \subseteq SUBSET RangeLarge
      /\ ~(SUBSET RangeLarge \subseteq SUBSET RangeMinusOne)
      /\ SUBSET SetX \subseteq SUBSET SetY
      /\ SUBSET SetY \subseteq SUBSET SetZ
      /\ ~(SUBSET SetZ \subseteq SUBSET SetY)
      /\ ~(SUBSET SetY \subseteq SUBSET SetX)
      /\ SUBSET Empty \subseteq SUBSET Empty
      /\ SUBSET Empty \subseteq SUBSET Singleton
      /\ SUBSET Empty \subseteq SUBSET RangeLarge
      /\ SUBSET Empty \subseteq SUBSET Nat
      /\ SUBSET Empty \subseteq SUBSET Int
      /\ ~(SUBSET Singleton \subseteq SUBSET Empty)
      /\ ~(SUBSET RangeLarge \subseteq SUBSET Empty)
      /\ ~(SUBSET Nat \subseteq SUBSET Empty)
      /\ ~(SUBSET Int \subseteq SUBSET Empty)
      /\ SUBSET Singleton \subseteq SUBSET Nat
      /\ SUBSET Singleton \subseteq SUBSET Int

Next == UNCHANGED ok

Spec == Init /\ [][Next]_ok

TypeOK == ok \in BOOLEAN
AllTestsHold == ok
Invariant == [](TypeOK /\ AllTestsHold)

=======================================================================================