---------------------------- MODULE BoundedCounterSystem ----------------------------
EXTENDS Naturals

CONSTANT Max

ASSUME MaxAssumption == Max = 3

VARIABLES
    count,   \* the subcomponent's local counter
    obs      \* the main controller's shared observable value (exposes count)

vars == << count, obs >>

TypeOK ==
    /\ count \in 0..Max
    /\ obs   \in 0..Max

-----------------------------------------------------------------------------
(* Subcomponent: a reusable bounded counting task                           *)

SubInit == count = 0

\* One increment per step, from 0 up to Max. The main controller exposes the
\* new local value as the shared observable value.
SubIncrement ==
    /\ count < Max
    /\ count' = count + 1
    /\ obs'   = count'

-----------------------------------------------------------------------------
(* Main controller                                                          *)

MainInit == obs = 0

\* The main controller may stutter only when the subcomponent is not enabled.
\* This step leaves the observable state unchanged.
MainStutter ==
    /\ ~ENABLED SubIncrement
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Combined system                                                          *)

Init ==
    /\ SubInit
    /\ MainInit

Next ==
    \/ SubIncrement
    \/ MainStutter

\* Persistent step relation with stuttering, plus weak fairness on the
\* subcomponent's increment action.
Fairness == WF_vars(SubIncrement)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety requirements                                                      *)

\* The observable value always reflects the subcomponent's local counter.
ObsMirrorsCount == obs = count

\* Initial observable value is 0.
InitialObsZero == obs = 0

\* The observable value stays within bounds.
ObsBounded == obs \in 0..Max

Invariants == TypeOK /\ ObsMirrorsCount /\ ObsBounded

\* The only changes to obs are increments by 1, made by the subcomponent
\* while it is enabled.
OnlyIncrementsChangeObs ==
    [][ obs' # obs => /\ obs < Max
                     /\ obs' = obs + 1
                     /\ SubIncrement ]_vars

\* Main controller stutter steps do not change the observable value.
StutterPreservesObs ==
    [][ MainStutter => obs' = obs ]_vars

\* The observable value never decreases.
ObsMonotonic == [][ obs' >= obs ]_vars

Safety ==
    /\ InitialObsZero
    /\ []Invariants
    /\ OnlyIncrementsChangeObs
    /\ StutterPreservesObs
    /\ ObsMonotonic

-----------------------------------------------------------------------------
(* Liveness requirement                                                     *)

ReachesMax == <>(obs = Max)

\* Once the maximum is reached, it is kept.
StaysAtMax == [](obs = Max => [](obs = Max))

Liveness == ReachesMax /\ StaysAtMax

-----------------------------------------------------------------------------
(* Proof obligations / properties to be checked                             *)

THEOREM SafetyTheorem   == Spec => Safety
THEOREM TypeTheorem     == Spec => []TypeOK
THEOREM LivenessTheorem == Spec => ReachesMax
THEOREM StabilityTheorem == Spec => StaysAtMax

=============================================================================