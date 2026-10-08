------------------------------- MODULE GrowingRepository -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS UNIVERSE

VARIABLES items

Init == items = {}

Next ==
  \/ /\ \E x \in UNIVERSE : ~x \in items
     /\ items' = items \cup {x}
  \/ items' = items

Spec ==
  /\ Init
  /\ [][Next]_<<items>>
  /\ WF_next(<<items>>)

Inv1 == items \subseteq UNIVERSE
Inv2 == Cardinality(items) = Cardinality({x \in items : x \in UNIVERSE})
Inv3 == \/ items = {}
         \/ (\E oldItems \in SUBSET UNIVERSE :
               /\ oldItems \subseteq items
               /\ oldItems \subseteq UNIVERSE
               /\ \A x \in items \ {oldItems} : ~x \in oldItems)

SpecWithInvariants ==
  Spec /\ Inv1 /\ Inv2 /\ Inv3

Fairness == WF_next(<<items>>)

EventuallyAllAdded ==
  \A x \in UNIVERSE : <>[](x \in items)

EventuallySomeAbsent ==
  \E x \in UNIVERSE : []<>(~x \in items)
=============================================================================