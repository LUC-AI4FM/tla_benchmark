---------------------------- MODULE ConcurrentStateSystem ----------------------------

EXTENDS Integers

CONSTANTS
    MaxValue,           \* Upper bound for the incrementing component (termination condition)
    ExternalConstant,   \* Externally supplied constant value
    StableInitValue     \* Initial value for the stable/unchanged component

VARIABLES
    counter,            \* The regularly updated (incrementing) component
    stable,             \* The component that remains unchanged during transitions
    fixed               \* Holds the externally supplied constant value

vars == <<counter, stable, fixed>>

\* Type invariant: all components hold values from their declared finite domains
TypeInvariant ==
    /\ counter \in 0..MaxValue
    /\ stable \in {StableInitValue}
    /\ fixed = ExternalConstant

\* Initialization predicate
Init ==
    /\ counter = 0                      \* Counter starts at 0
    /\ stable = StableInitValue         \* Stable component gets its initial value
    /\ fixed = ExternalConstant         \* Fixed component holds the external constant

\* Guard that enables the increment step
IncrementEnabled ==
    counter < MaxValue

\* The increment action: increments counter, leaves stable unchanged
Increment ==
    /\ IncrementEnabled                 \* Guard: only enabled when below max
    /\ counter' = counter + 1           \* Increment the counter
    /\ UNCHANGED stable                 \* Explicitly state stable doesn't change
    /\ UNCHANGED fixed                  \* Explicitly state fixed doesn't change

\* Termination condition reached - system can stutter
Terminated ==
    /\ counter = MaxValue
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ Increment
    \/ Terminated

\* Fairness: weak fairness on Increment ensures progress when enabled
Fairness ==
    WF_vars(Increment)

\* Complete specification with fairness
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* Safety: the stable component never changes value while incrementing is enabled
StableNeverChanges ==
    stable = StableInitValue

\* Safety: the external constant remains equal to its initial supplied value
ConstantNeverChanges ==
    fixed = ExternalConstant

\* Combined safety invariant
SafetyInvariant ==
    /\ StableNeverChanges
    /\ ConstantNeverChanges

--------------------------------------------------------------------------------
\* INVARIANTS
--------------------------------------------------------------------------------

\* Main invariant: type correctness plus safety
Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant

\* Counter is always within bounds
CounterBounded ==
    counter >= 0 /\ counter <= MaxValue

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* Progress: incrementing action enabled repeatedly until termination
\* From any state where increment is enabled, eventually we reach termination
ProgressToTermination ==
    IncrementEnabled ~> (counter = MaxValue)

\* Liveness: from any reachable state where the guard holds,
\* eventually a state with the incremented value is reached
LivenessIncrement ==
    \A v \in 0..(MaxValue-1) :
        (counter = v /\ IncrementEnabled) ~> (counter > v)

\* Eventually termination is reached
EventuallyTerminates ==
    <>(counter = MaxValue)

--------------------------------------------------------------------------------
\* THEOREMS (properties to check)
--------------------------------------------------------------------------------

\* The specification maintains the invariant
THEOREM Spec => []Invariant

\* The specification ensures progress to termination
THEOREM Spec => ProgressToTermination

\* The specification ensures eventual termination
THEOREM Spec => EventuallyTerminates

================================================================================