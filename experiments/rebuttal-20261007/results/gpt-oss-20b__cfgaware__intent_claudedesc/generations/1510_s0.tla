------------------------------ MODULE CaseExample ------------------------------
EXTENDS Naturals

CONSTANTS Domain, SpecificValue, SpecificKey, DesignatedConstant

VARIABLES chosenVar, f

(* Initial state *)
Init == 
  /\ chosenVar \in Domain
  /\ f = [x \in Domain |-> 0]
  /\ chosenVar = SpecificValue

(* Next-state relation using CASE with OTHER clause *)
Next ==
  /\ chosenVar' = chosenVar
  /\ f' = CASE chosenVar = SpecificValue ->
              [f EXCEPT ![SpecificKey] = DesignatedConstant]
           [] OTHER ->
              f

Spec == Init /\ [][Next]_<<chosenVar, f>>

==============================================================================