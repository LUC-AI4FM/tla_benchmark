```
MODULE SimpleStateTransformer
EXTENDS Integers

CONSTANTS ControlValues, DistinguishedValue, Constant
VARIABLES control, vector

Init == (control \in ControlValues) /\ (vector = <<0, 0, 0, 0, 0>>)

Next == IF control = DistinguishedValue
           THEN vector' = [vector EXCEPT ![DistinguishedValue] = Constant]
           ELSE vector' = vector
       /\ control' = control

Spec == Init /\ [][Next]_<<control, vector>>

ControlInvariant == [](control' = control)
VectorUpdate == []((control = DistinguishedValue) => (vector'[DistinguishedValue] = Constant))
VectorNoSpontaneousChange == []((control # DistinguishedValue) => (vector' = vector))

THEOREM Spec => []ControlInvariant
THEOREM Spec => []VectorUpdate
THEOREM Spec => []VectorNoSpontaneousChange

=============================================================================
```
Note: The `THEOREM` statements are used to assert the desired temporal properties. These can be verified using a model checker such as TLC.