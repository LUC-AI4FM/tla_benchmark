------------------------------- MODULE StateTransformer -------------------------------

CONSTANTS 
    ControlValues,          \* The set of possible control values (should be a subset of integers)
    DistinguishedValue,     \* The distinguished value in ControlValues that triggers updates
    FixedConstant           \* The constant to write into the vector when triggered

VARIABLES 
    ctrl,                   \* The control value
    vec                     \* The vector of counters

Init == /\ ctrl \in ControlValues
        /\ vec = <<0, 0, 0, 0, 0>>

Next == \/ /\ ctrl = DistinguishedValue
            /\ vec' = [vec EXCEPT ![DistinguishedValue] = FixedConstant]
         \/ /\ ctrl /= DistinguishedValue
            /\ vec' = vec

Spec == Init /\ [][Next]_<<ctrl, vec>>

\* Temporal properties
CONSTANT Property1, Property2, Property3, Property4

Property1 == \A s \in States: s.ctrl = [s]'ctrl

Property2 == \A s \in States: \A i \in 1..5: s.vec[i] \in Int

Property3 == \A s \in States: 
                \/ s.ctrl /= DistinguishedValue
                \/ s'.vec[s.ctrl] = FixedConstant

Property4 == \A s \in States:
                \/ s.ctrl = DistinguishedValue
                \/ s'.vec = s.vec

THEOREM Spec => Property1 /\ Property2 /\ Property3 /\ Property4

=============================================================================