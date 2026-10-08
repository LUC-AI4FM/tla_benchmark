------------------------------- MODULE SimpleSystem -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* The externally supplied constant value
    EXTERNAL_CONSTANT,
    
    \* The bound for the incrementing component
    BOUND,

    \* Domains for the components
    DOMAIN_REGULAR,
    DOMAIN_UNCHANGED

VARIABLES 
    RegularComponent,
    UnchangedComponent

Init == /\ RegularComponent = 0
        /\ UnchangedComponent \in DOMAIN_UNCHANGED
        /\ EXTERNAL_CONSTANT \in DOMAIN_REGULAR

Next ==
    \/ /\ RegularComponent < BOUND
       /\ RegularComponent' = RegularComponent + 1
       /\ UnchangedComponent' = UnchangedComponent
       /\ EXTERNAL_CONSTANT' = EXTERNAL_CONSTANT
    \/ /\ RegularComponent >= BOUND
       /\ RegularComponent' = RegularComponent
       /\ UnchangedComponent' = UnchangedComponent
       /\ EXTERNAL_CONSTANT' = EXTERNAL_CONSTANT

Spec ==
    Init /\ [][Next]_<<RegularComponent, UnchangedComponent>>

\* Safety properties
UnchangedStable == \A s \in States : s.UnchangedComponent = Init.UnchangedComponent
ExternalConstantStable == \A s \in States : s.EXTERNAL_CONSTANT = EXTERNAL_CONSTANT

\* Invariant: all components always hold values from their declared finite domains
Invariant ==
    /\ RegularComponent \in DOMAIN_REGULAR
    /\ UnchangedComponent \in DOMAIN_UNCHANGED
    /\ EXTERNAL_CONSTANT \in DOMAIN_REGULAR

\* Liveness property: from any reachable state where the incrementing guard holds, eventually a state with the incremented value is reached.
IncrementLiveness == 
    [](RegularComponent < BOUND) ~> <>(RegularComponent' = RegularComponent + 1)

=============================================================================