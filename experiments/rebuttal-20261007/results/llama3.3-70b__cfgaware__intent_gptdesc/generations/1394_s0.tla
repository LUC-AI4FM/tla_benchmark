---------------------------- MODULE Spec ----------------------------
EXTENDS Integers

CONSTANT ConstantValue, InitRegular, InitUnchanged
VARIABLE Regular, Unchanged

Init == (Regular = InitRegular) /\ (Unchanged = InitUnchanged)

TypeInvariant == Regular \in 0..100 /\ Unchanged \in {1, 2, 3}

Next == (Regular' = Regular + 1) /\ (Unchanged' = Unchanged) /\ (ConstantValue' = ConstantValue)
       /\ (Regular < 100)

Spec == Init /\ [][Next]_<<Regular, Unchanged, ConstantValue>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => <>[](Regular = 100)
====================================================================