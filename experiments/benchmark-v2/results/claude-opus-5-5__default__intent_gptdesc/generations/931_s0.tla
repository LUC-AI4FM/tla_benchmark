---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

CONSTANT NumHours          \* Number of distinct hour values (intended: 24)

ASSUME NumHoursAssumption == NumHours = 24

VARIABLE hr                \* The current hour shown on the clock

vars == <<hr>>

Hours == 0 .. (NumHours - 1)

-----------------------------------------------------------------------------
(* Initialization: the hour is any valid integer in 0..23.                  *)
Init == hr \in Hours

(* Advance step: increment the hour by one, modulo 24.                      *)
Advance == hr' = (hr + 1) % NumHours

Next == Advance

(* Specification: stuttering steps are permitted by [Next]_vars.            *)
(* Strong fairness ensures the advance step is never postponed forever.     *)
Spec == Init /\ [][Next]_vars /\ SF_vars(Advance)

-----------------------------------------------------------------------------
(* SAFETY                                                                   *)

(* The hour is always an integer in 0..23.                                  *)
TypeOK == hr \in Hours

HourInRange == []TypeOK

(* Determinacy of the wrap-around behavior: from 23 the next hour is 0;     *)
(* from any h in 0..22 the next hour is h + 1. Stated as an action          *)
(* property over every non-stuttering step.                                 *)
WrapAroundStep ==
    /\ (hr = NumHours - 1) => (hr' = 0)
    /\ (hr \in 0 .. (NumHours - 2)) => (hr' = hr + 1)

WrapAround == [][WrapAroundStep]_vars

(* Stuttering tolerance: every step either leaves the hour unchanged or is  *)
(* a correct advancement; stuttering steps preserve the range invariant.    *)
StutterOrAdvance == UNCHANGED hr \/ WrapAroundStep

StutterPreservesSafety == (UNCHANGED hr /\ TypeOK) => TypeOK'

StutteringTolerance ==
    /\ [][StutterOrAdvance]_vars
    /\ [][StutterPreservesSafety]_vars

-----------------------------------------------------------------------------
(* LIVENESS                                                                 *)

(* Progress: every hour value recurs infinitely often.                      *)
EveryHourRecurs == \A h \in Hours : []<>(hr = h)

(* From any reachable state, every hour value is eventually reached.        *)
EventuallyReachEveryHour == \A h \in Hours : [](TRUE ~> (hr = h))

(* Fairness / non-postponement: the hour eventually changes whenever the    *)
(* advance step is enabled (which it always is).                            *)
AdvanceNotPostponed == \A h \in Hours : (hr = h) ~> (hr # h)

-----------------------------------------------------------------------------
(* THEOREMS                                                                 *)

THEOREM Spec => HourInRange
THEOREM Spec => WrapAround
THEOREM Spec => StutteringTolerance
THEOREM Spec => EveryHourRecurs
THEOREM Spec => EventuallyReachEveryHour
THEOREM Spec => AdvanceNotPostponed
=============================================================================