---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences

CONSTANTS IndexSet, ControlValues, DistinguishedValue, FixedConstant

VARIABLES control, vector

vars == <<control, vector>>

TypeOK ==
    /\ control \in ControlValues
    /\ vector \in [IndexSet -> Int]

Init ==
    /\ control \in ControlValues
    /\ vector = [i \in IndexSet |-> 0]

UpdateVector ==
    /\ control = DistinguishedValue
    /\ vector' = [vector EXCEPT ![DistinguishedValue] = FixedConstant]
    /\ UNCHANGED control

NoChange ==
    /\ control # DistinguishedValue
    /\ UNCHANGED <<control, vector>>

Next ==
    \/ UpdateVector
    \/ NoChange

Spec == Init /\ [][Next]_vars

ControlInvariant == control \in ControlValues

VectorIntegerInvariant == \A i \in IndexSet : vector[i] \in Int

ControlNeverChanges == [][control' = control]_vars

VectorUpdateProperty ==
    [][(control = DistinguishedValue) => 
       (vector' = [vector EXCEPT ![DistinguishedValue] = FixedConstant])]_vars

VectorNoChangeProperty ==
    [][(control # DistinguishedValue) => (vector' = vector)]_vars

Safety ==
    /\ ControlInvariant
    /\ VectorIntegerInvariant

Invariant == TypeOK /\ ControlInvariant

=============================================================================