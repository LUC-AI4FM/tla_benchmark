------------------------------- MODULE StateTransformer -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS CtrlSet, DistinguishedValue, FixedConstant
ASSUME CtrlSet \in SUBSET Integers /\ Cardinality(CtrlSet) = 5
ASSUME DistinguishedValue \in CtrlSet
ASSUME FixedConstant \in Integers

VARIABLES ctrl, vec

Init == /\ ctrl \in CtrlSet
        /\ vec \in [1..5 -> 0]

Next ==
    \/ /\ ctrl = DistinguishedValue
       /\ \E i \in 1..5 : vec' = [vec EXCEPT ![i] = FixedConstant]
          /\ \A j \in 1..5 \ {i} : vec'[j] = vec[j]
    \/ /\ ctrl \notin DistinguishedValue
       /\ vec' = vec

Spec == Init /\ [][Next]_<<ctrl, vec>>

CONSTRAINTS Spec

THEOREM Spec => [](ctrl = <<ctrl>>_0)

THEOREM Spec => [](vec \in [1..5 -> Integers])

THEOREM Spec => <>(ctrl = DistinguishedValue) ~> (vec[ctrl] = FixedConstant)

THEOREM Spec => [](ctrl \notin DistinguishedValue) ~> (vec' = vec)
=====================================================================================