MODULE CounterSystem
EXTENDS Naturals

VARIABLE outerX

(* Inner step definition *)
Step == outerX < 3 /\ outerX' = outerX + 1
NextInner == Step \/ UNCHANGED outerX
WF_Step == WF_vars <<outerX>> Step

Init == outerX = 0
Next == NextInner

Spec == Init /\ [][Next] /\ WF_Step /\ <> (outerX = 3)