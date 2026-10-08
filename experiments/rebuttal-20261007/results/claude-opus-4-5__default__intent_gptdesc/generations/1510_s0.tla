---------------------------- MODULE StateTransformer ----------------------------
EXTENDS Integers, Sequences

CONSTANTS 
    IndexSet,           \* The set of five indices {0, 1, 2, 3, 4}
    ControlSet,         \* The set of five control values {0, 1, 2, 3, 4}
    DistinguishedValue, \* The distinguished control value
    FixedConstant       \* The fixed constant to write

VARIABLES 
    control,  \* The control value (invariant across steps)
    vector    \* The vector of five integer counters

ASSUME IndexSet = {0, 1, 2, 3, 4}
ASSUME ControlSet = {0, 1, 2, 3, 4}
ASSUME DistinguishedValue \in ControlSet
ASSUME DistinguishedValue \in IndexSet
ASSUME FixedConstant \in Int

vars == <<control, vector>>

TypeOK ==
    /\ control \in ControlSet
    /\ vector \in [IndexSet -> Int]

Init ==
    /\ control \in ControlSet
    /\ vector = [i \in IndexSet |-> 0]

UpdateVector ==
    /\ control = DistinguishedValue
    /\ vector' = [vector EXCEPT ![DistinguishedValue] = FixedConstant]
    /\ UNCHANGED control

KeepVector ==
    /\ control # DistinguishedValue
    /\ UNCHANGED <<control, vector>>

Next ==
    \/ UpdateVector
    \/ KeepVector

Spec == Init /\ [][Next]_vars

\* Safety Invariant 1: The control value never changes (captured by TypeOK and invariance)
ControlInvariant == control \in ControlSet

\* Safety Invariant 2: Vector entries are always integers
VectorIntegerInvariant == \A i \in IndexSet : vector[i] \in Int

\* Combined type invariant
Inv == TypeOK

\* Safety Property 3: If control equals distinguished value, then in next state 
\* the corresponding entry has the fixed constant
DistinguishedUpdateProperty ==
    [](control = DistinguishedValue => [][vector'[DistinguishedValue] = FixedConstant]_vars)

\* Safety Property 4: If control does not equal distinguished value, 
\* then all vector entries remain unchanged
NonDistinguishedPreservationProperty ==
    [](control # DistinguishedValue => [][vector' = vector]_vars)

\* The control value remains constant across all transitions
ControlNeverChanges == [][control' = control]_vars

\* Vector entries only change as specified: only the distinguished index can change,
\* and only when control equals the distinguished value
VectorChangeOnlyAsSpecified ==
    [][\A i \in IndexSet : 
        (i # DistinguishedValue \/ control # DistinguishedValue) 
        => vector'[i] = vector[i]]_vars

\* When control equals distinguished value and a step occurs, 
\* the corresponding entry becomes the fixed constant
ImmediateUpdateWhenDistinguished ==
    [][control = DistinguishedValue => vector'[DistinguishedValue] = FixedConstant]_vars

\* When control does not equal distinguished value, vector is unchanged
PreservationWhenNotDistinguished ==
    [][control # DistinguishedValue => vector' = vector]_vars

\* All safety properties combined
Safety ==
    /\ Inv
    /\ ControlNeverChanges
    /\ VectorChangeOnlyAsSpecified
    /\ ImmediateUpdateWhenDistinguished
    /\ PreservationWhenNotDistinguished

=============================================================================