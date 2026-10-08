------------------------------- MODULE SimpleSystem -------------------------------

CONSTANTS 
    \* The externally supplied constant value
    EXTERNAL_CONSTANT,

    \* The initial values for the components
    INIT_REGULAR,
    INIT_STABLE,
    
    \* The bound on the incrementing component
    BOUND

VARIABLES 
    \* The regularly updated component
    Regular,
    
    \* The component that may be left unchanged
    Stable

ASSUME 
    \* Ensure initial values are within their domains
    /\ INIT_REGULAR \in 0..BOUND
    /\ INIT_STABLE \in 0..100  \* Assuming a reasonable domain for the stable component
    /\ EXTERNAL_CONSTANT \in 0..100  \* Assuming a reasonable domain for the external constant

CONSTANTS 
    \* The domains of the components
    DOMAIN_REGULAR,
    DOMAIN_STABLE

ASSUME 
    \* Ensure initial values are within their declared domains
    /\ INIT_REGULAR \in DOMAIN_REGULAR
    /\ INIT_STABLE \in DOMAIN_STABLE

VARIABLES State

Init == 
    /\ Regular = INIT_REGULAR
    /\ Stable = INIT_STABLE

Next ==
    \/ \* Increment the regular component while keeping the stable component unchanged
       /\ Regular < BOUND
       /\ Regular' = Regular + 1
       /\ Stable' = Stable
       
Spec == 
    Init /\ [][Next]_<<Regular, Stable>>

\* Invariants
InvRegDomain == Regular \in DOMAIN_REGULAR
InvStableDomain == Stable \in DOMAIN_STABLE
InvExternalConstant == EXTERNAL_CONSTANT = EXTERNAL_CONSTANT

TypeInvariant == InvRegDomain /\ InvStableDomain /\ InvExternalConstant

\* Liveness property: from any state where the incrementing guard holds, eventually a state with the incremented value is reached.
IncrementLiveness ==
    [](Regular < BOUND) -> <>[](Regular' = Regular + 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => IncrementLiveness

=============================================================================