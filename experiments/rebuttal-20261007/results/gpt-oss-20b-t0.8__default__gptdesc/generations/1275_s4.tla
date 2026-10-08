MODULE SingleVarInit
EXTENDS Integers

VARIABLE s

(*--- Initialization Predicate ---*)
Init == \E v \in 0..1 : (v < 1) /\ (s = v)

(*--- Next-State Relation: no change to s ---*)
Next == UNCHANGED <<s>>

(*--- Specification: Initial condition and invariant evolution ---*)
Spec == Init /\ [][Next]_<<s>>

(*--- Safety Invariant ---*)
Inv == s < 1

THEOREM Spec_Inv : Spec => []Inv
===============================================================================