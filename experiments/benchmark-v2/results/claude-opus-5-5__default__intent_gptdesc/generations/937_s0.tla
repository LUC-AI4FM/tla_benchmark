---------------------------- MODULE HourClock ----------------------------
(***************************************************************************)
(* A simple discrete hour clock that cycles forever through 1..12.        *)
(* The only state is the current hour `hr`. Each advancing step moves     *)
(* the hour to its successor modulo 12, so 12 is followed by 1.           *)
(* Weak fairness on the advancing action guarantees perpetual progress.   *)
(* No external scheduling assumption is needed.                            *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES hr

vars == << hr >>

Hours == 1..12

(***************************************************************************)
(* Successor of an hour, modulo 12, with 12 followed by 1.                *)
(***************************************************************************)
NextHour(h) == (h % 12) + 1

(***************************************************************************)
(* Type and bounds invariant.                                              *)
(***************************************************************************)
TypeOK == hr \in Hours

(***************************************************************************)
(* Initial condition: the clock may start at any legal hour.              *)
(***************************************************************************)
Init == hr \in Hours

(***************************************************************************)
(* The single advancing step.                                              *)
(***************************************************************************)
Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

(***************************************************************************)
(* Temporal specification: initial condition, the step relation (with    *)
(* stuttering), and weak fairness enforcing that the clock never stops.   *)
(* Tick is always enabled, so WF forces infinitely many Tick steps.       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* (1) The hour is always an integer in 1..12. *)
TypeInvariant == []TypeOK

(* Every non-stuttering step advances the hour to its successor mod 12. *)
StepCorrect == [][hr' = NextHour(hr)]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

(* (2) Infinitely many advancing (non-stuttering) steps occur. *)
InfinitelyManyTicks == []<><<Tick>>_vars

(* (3) Every hour value appears infinitely often. *)
EveryHourInfinitelyOften == \A h \in Hours : []<>(hr = h)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems (model-checkable with TLC: INVARIANT TypeOK; PROPERTIES        *)
(* StepCorrect, InfinitelyManyTicks, EveryHourInfinitelyOften).            *)
(***************************************************************************)

THEOREM TypeCorrectness == Spec => TypeInvariant

THEOREM StepCorrectness == Spec => StepCorrect

THEOREM Progress == Spec => InfinitelyManyTicks

THEOREM AllHoursRecur == Spec => EveryHourInfinitelyOften

=============================================================================