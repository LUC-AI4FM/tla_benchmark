---------------------------- MODULE CounterLoop ----------------------------

EXTENDS Integers

CONSTANTS Bound

ASSUME BoundAssumption == Bound \in Nat /\ Bound > 0

VARIABLES counter, state

vars == <<counter, state>>

TypeInvariant ==
    /\ counter \in 0..Bound
    /\ state \in {"running", "terminated"}

Init ==
    /\ counter = 0
    /\ state = "running"

Increment ==
    /\ state = "running"
    /\ counter < Bound
    /\ counter' = counter + 1
    /\ IF counter' = Bound
       THEN state' = "terminated"
       ELSE state' = "running"

Idle ==
    /\ state = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ Increment
    \/ Idle

Fairness == WF_vars(Increment)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

CounterNeverDecreases ==
    [][counter' >= counter]_vars

CounterIncrementsAtMostByOne ==
    [][counter' \in {counter, counter + 1}]_vars

CounterNeverExceedsBound ==
    counter <= Bound

SafetyInvariant ==
    /\ TypeInvariant
    /\ CounterNeverExceedsBound

TerminationImpliesCounterAtBound ==
    state = "terminated" => counter = Bound

CounterAtBoundImpliesTermination ==
    counter = Bound => state = "terminated"

ConsistencyInvariant ==
    /\ TerminationImpliesCounterAtBound
    /\ CounterAtBoundImpliesTermination

TerminatedRemainsSo ==
    [](state = "terminated" => [](state = "terminated"))

CounterStableAfterTermination ==
    [](state = "terminated" => [](counter = Bound))

EventualTermination ==
    <>(state = "terminated")

EventuallyReachesBound ==
    <>(counter = Bound)

IntermediateValueReachable ==
    <>(counter = 5)

FinalTransitionPossible ==
    <>(counter = Bound - 1 /\ state = "running")

AllValuesReachable ==
    \A v \in 0..Bound : <>(counter = v)

MonotonicProgress ==
    \A v \in 0..(Bound-1) : (counter = v) ~> (counter > v)

IncrementEnabled == state = "running" /\ counter < Bound

ProgressUnderFairness ==
    IncrementEnabled ~> (counter > counter \/ state = "terminated")

NoDeadlockBeforeTermination ==
    (state = "running") => ENABLED Increment

=============================================================================