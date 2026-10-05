---------------------------- MODULE Clock12Hour ----------------------------
EXTENDS Naturals

CONSTANTS Hours

ASSUME HoursAssumption == Hours = 1..12

VARIABLES hour

-----------------------------------------------------------------------------
(* Type invariant: hour is always a valid value in 1..12 *)
TypeInvariant == hour \in 1..12

-----------------------------------------------------------------------------
(* Initial state: any valid hour *)
Init == hour \in 1..12

-----------------------------------------------------------------------------
(* Next state: increment-or-wrap formulation *)
NextIncrementOrWrap ==
    hour' = IF hour = 12 THEN 1 ELSE hour + 1

(* Next state: modular arithmetic formulation *)
NextModular ==
    hour' = (hour % 12) + 1

(* The main Next relation uses the increment-or-wrap formulation *)
Next == NextIncrementOrWrap

-----------------------------------------------------------------------------
(* Equivalence property: both formulations produce the same result *)
TransitionEquivalence ==
    [](NextIncrementOrWrap <=> NextModular)

(* Alternative: state-based equivalence check *)
ModularResult == (hour % 12) + 1
IncrementOrWrapResult == IF hour = 12 THEN 1 ELSE hour + 1

ResultEquivalence == ModularResult = IncrementOrWrapResult

-----------------------------------------------------------------------------
(* Safety invariant: hour always remains valid *)
SafetyInvariant == TypeInvariant

(* Additional safety: the computed next hour would also be valid *)
NextHourValid == 
    (IF hour = 12 THEN 1 ELSE hour + 1) \in 1..12

-----------------------------------------------------------------------------
(* Liveness: the clock always eventually advances *)
AlwaysAdvances == []<>(hour' # hour)

(* Liveness: every hour is visited infinitely often *)
VisitsHour(h) == []<>(hour = h)

AllHoursVisited == \A h \in 1..12 : VisitsHour(h)

(* Liveness: from any hour, eventually reaches the next hour *)
EventuallyNext(h) == 
    LET nextHour == IF h = 12 THEN 1 ELSE h + 1
    IN [](hour = h => <>(hour = nextHour))

Progress == \A h \in 1..12 : EventuallyNext(h)

-----------------------------------------------------------------------------
(* Fairness: weak fairness ensures the clock keeps ticking *)
Fairness == WF_hour(Next)

(* Full specification with fairness *)
Spec == Init /\ [][Next]_hour /\ Fairness

(* Specification without fairness (for safety checking only) *)
SpecSafety == Init /\ [][Next]_hour

-----------------------------------------------------------------------------
(* Theorems to verify *)

(* Safety theorem: TypeInvariant is always maintained *)
THEOREM SafetyTheorem == Spec => []TypeInvariant

(* Equivalence theorem: both transition formulations are equivalent *)
THEOREM EquivalenceTheorem == TypeInvariant => ResultEquivalence

(* Liveness theorem: all hours are visited infinitely often *)
THEOREM LivenessTheorem == Spec => AllHoursVisited

(* Progress theorem: clock always makes progress *)
THEOREM ProgressTheorem == Spec => Progress

=============================================================================