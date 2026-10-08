---------------------------- MODULE Specification ----------------------------

EXTENDS Naturals

CONSTANT ExternalConstant

VARIABLES incrementingComponent, unchangedComponent, constantComponent

vars == <<incrementingComponent, unchangedComponent, constantComponent>>

\* Finite domains for each component
IncrementingDomain == 0..10
UnchangedDomain == {0, 1, 2}
ConstantDomain == {100, 200, 300}

\* Termination bound for the incrementing component
TerminationBound == 10

\* Type invariant: all components hold values from their declared finite domains
TypeInvariant ==
    /\ incrementingComponent \in IncrementingDomain
    /\ unchangedComponent \in UnchangedDomain
    /\ constantComponent \in ConstantDomain

\* Initial state predicate
Init ==
    /\ incrementingComponent = 0
    /\ unchangedComponent \in UnchangedDomain
    /\ constantComponent = ExternalConstant

\* Guard that enables the increment step
IncrementEnabled ==
    incrementingComponent < TerminationBound

\* Increment action: increments the regularly-updated component
\* while explicitly leaving unchanged component stable
Increment ==
    /\ IncrementEnabled
    /\ incrementingComponent' = incrementingComponent + 1
    /\ UNCHANGED unchangedComponent
    /\ UNCHANGED constantComponent

\* Termination state: no more increments possible
Terminated ==
    /\ ~IncrementEnabled
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ Increment
    \/ Terminated

\* Fairness condition for liveness
Fairness == WF_vars(Increment)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety property: unchanged component never changes while incrementing is enabled
SafetyUnchanged ==
    [][IncrementEnabled => (unchangedComponent' = unchangedComponent)]_vars

\* Safety property: external constant remains equal to its initial value
SafetyConstant ==
    [](constantComponent = ExternalConstant)

\* Combined safety property
Safety ==
    /\ SafetyUnchanged
    /\ SafetyConstant

\* Progress property: incrementing action enabled until termination
Progress ==
    [](IncrementEnabled => (ENABLED Increment))

\* Liveness property: from any state where guard holds, eventually reach incremented value
Liveness ==
    \A n \in IncrementingDomain :
        [](incrementingComponent = n /\ IncrementEnabled => 
           <>(incrementingComponent = n + 1))

\* Main invariant combining type safety
Invariant == TypeInvariant

=============================================================================