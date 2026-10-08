```
MODULE RegionMapping
EXTENDS Integers, Sequences, TLC

CONSTANTS Regions, Locations, TranslationObjects
VARIABLES currentRegion, locationStack, translationObject

Init ==
  /\ currentRegion = "Start"
  /\ locationStack = << >>
  /\ translationObject = [r \in Regions |-> << >>]

Next ==
  /\ IF currentRegion = "Start"
     THEN
       /\ currentRegion' = "TLAPlus"
       /\ locationStack' = Append(locationStack, "Start")
       /\ translationObject' = [r \in Regions |-> << r, "Start" >>]
     ELSE
       /\ currentRegion' = "PlusCal"
       /\ locationStack' = Append(locationStack, "TLAPlus")
       /\ WITH p == GetParenthesisDepth(currentRegion)
         |\ translationObject' = [r \in Regions |-> IF r = currentRegion THEN Append(translationObject[r], p) ELSE translationObject[r]]
  /\ IF currentRegion = "End"
     THEN
       /\ currentRegion' = "Start"
       /\ locationStack' = << >>
       /\ translationObject' = [r \in Regions |-> << >>]

Spec == Init /\ [][Next]_

WellFormed ==
  /\ currentRegion \in Regions
  /\ locationStack \subseteq Locations
  /\ translationObject \in [Regions -> Sequences(Locations)]

ParenthesisMatch ==
  /\ GetParenthesisDepth(currentRegion) = 0

TokenOrdering ==
  /\ TokenPositions(translationObject) = Sort(TokenPositions(translationObject))

CorrectMapping ==
  /\ currentRegion = "PlusCal" => locationStack[Len(locationStack) - 1] = translationObject[currentRegion][Len(translationObject[currentRegion]) - 1]

SafetyInv ==
  /\ WellFormed
  /\ ParenthesisMatch
  /\ TokenOrdering
  /\ CorrectMapping

THEOREM Spec => []SafetyInv

GetParenthesisDepth(r) == 
  LET open == {p \in locationStack : p = "("}
      close == {p \in locationStack : p = ")"}
  IN Cardinality(open) - Cardinality(close)

TokenPositions(t) == [x \in DOMAIN t |-> Len(t[x])]

FAIRNESS Spec
```