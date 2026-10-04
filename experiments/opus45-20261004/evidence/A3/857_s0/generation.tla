---------------------------- MODULE PrisonerLightSwitch ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    N,              \* Number of prisoners (including the counter)
    Counter,        \* The designated counter prisoner (in 1..N)
    KnownInitial    \* TRUE if initial light state is known to be off, FALSE otherwise

VARIABLES
    light,          \* State of the lamp: TRUE = on, FALSE = off
    count,          \* Counter's count of signals received
    signaled,       \* Function: signaled[p] = number of times prisoner p has signaled
    visited,        \* Set of prisoners who have visited the cell
    announced,      \* TRUE if victory has been announced
    inCell          \* The prisoner currently in the cell (or 0 if none)

vars == <<light, count, signaled, visited, announced, inCell>>

Prisoners == 1..N

TypeOK ==
    /\ light \in BOOLEAN
    /\ count \in Nat
    /\ signaled \in [Prisoners -> Nat]
    /\ visited \subseteq Prisoners
    /\ announced \in BOOLEAN
    /\ inCell \in Prisoners \cup {0}

\* Maximum number of times a non-counter prisoner can signal
MaxSignals == IF KnownInitial THEN 1 ELSE 2

\* Threshold count needed for the counter to announce victory
Threshold == IF KnownInitial THEN N - 1 ELSE 2 * N - 1

\* Initial state
Init ==
    /\ light = IF KnownInitial THEN FALSE ELSE FALSE  \* In unknown case, could be either
    /\ count = 0
    /\ signaled = [p \in Prisoners |-> 0]
    /\ visited = {}
    /\ announced = FALSE
    /\ inCell = 0

\* For the unknown initial state variant, we also consider initial light being on
InitUnknown ==
    /\ light \in BOOLEAN
    /\ count = 0
    /\ signaled = [p \in Prisoners |-> 0]
    /\ visited = {}
    /\ announced = FALSE
    /\ inCell = 0

\* Warden selects a prisoner to enter the cell
WardenSelect(p) ==
    /\ ~announced
    /\ inCell = 0
    /\ inCell' = p
    /\ visited' = visited \cup {p}
    /\ UNCHANGED <<light, count, signaled, announced>>

\* Counter prisoner's action when in the cell
CounterAction ==
    /\ inCell = Counter
    /\ ~announced
    /\ \/ \* Counter sees light on: turn it off and increment count
          /\ light = TRUE
          /\ light' = FALSE
          /\ count' = count + 1
          /\ IF count' >= Threshold
             THEN announced' = TRUE
             ELSE announced' = FALSE
          /\ UNCHANGED signaled
       \/ \* Counter sees light off: do nothing (or could turn on but strategy says no)
          /\ light = FALSE
          /\ UNCHANGED <<light, count, signaled, announced>>
    /\ inCell' = 0
    /\ UNCHANGED visited

\* Non-counter prisoner's action when in the cell
NonCounterAction(p) ==
    /\ inCell = p
    /\ p /= Counter
    /\ ~announced
    /\ \/ \* Light is off and haven't signaled max times: turn light on
          /\ light = FALSE
          /\ signaled[p] < MaxSignals
          /\ light' = TRUE
          /\ signaled' = [signaled EXCEPT ![p] = @ + 1]
          /\ UNCHANGED <<count, announced>>
       \/ \* Light is on or already signaled max times: do nothing
          /\ \/ light = TRUE
             \/ signaled[p] >= MaxSignals
          /\ UNCHANGED <<light, count, signaled, announced>>
    /\ inCell' = 0
    /\ UNCHANGED visited

\* Combined next state relation
Next ==
    \/ \E p \in Prisoners : WardenSelect(p)
    \/ CounterAction
    \/ \E p \in Prisoners \ {Counter} : NonCounterAction(p)

\* Fairness: weak fairness on warden selecting each prisoner
\* This ensures each prisoner is selected infinitely often
Fairness ==
    /\ \A p \in Prisoners : WF_vars(WardenSelect(p))
    /\ WF_vars(CounterAction)
    /\ \A p \in Prisoners \ {Counter} : WF_vars(NonCounterAction(p))

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Specification for unknown initial light state
SpecUnknown == InitUnknown /\ [][Next]_vars /\ Fairness

\* Safety: If victory is announced, all prisoners must have visited
SafetyInvariant ==
    announced => (visited = Prisoners)

\* Liveness: Eventually victory is announced
LivenessProperty ==
    <>(announced = TRUE)

\* Additional invariant: count never exceeds threshold + some buffer for unknown case
CountBound ==
    count <= 2 * N

\* Invariant: signaled counts are bounded
SignaledBound ==
    \A p \in Prisoners : signaled[p] <= MaxSignals

===================================================================================