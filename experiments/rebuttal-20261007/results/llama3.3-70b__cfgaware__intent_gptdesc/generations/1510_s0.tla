---------------------------- MODULE SimpleStateTransformer ----------------------------
EXTENDS Integers

CONSTANT ControlValues, IndexSet, DistinguishedValue, FixedConstant
VARIABLE control, vector

Init == (control \in ControlValues) /\ (vector = [i \in IndexSet |-> 0])

Next == IF control = DistinguishedValue
        THEN vector' = [vector EXCEPT ![DistinguishedValue] = FixedConstant]
        ELSE vector' = vector
        ENDIF
      /\ control' = control

Spec == Init /\ [][Next]_<<control, vector>>

THEOREM Spec => []<>(control = DistinguishedValue => vector[DistinguishedValue] = FixedConstant)
THEOREM Spec => []<>(control # DistinguishedValue => vector' = vector)

=============================================================================