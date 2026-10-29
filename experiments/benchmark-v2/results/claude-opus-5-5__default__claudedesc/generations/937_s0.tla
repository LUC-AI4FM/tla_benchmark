------------------------------ MODULE HourClock2 ------------------------------
(***************************************************************************)
(* Adds liveness to the basic hour-clock specification from HourClock.    *)
(* HourClock declares the variable hr and defines:                         *)
(*   HCini == hr \in (1..12)                                               *)
(*   HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1                          *)
(*   HC    == HCini /\ [][HCnxt]_hr                                        *)
(***************************************************************************)
EXTENDS HourClock

(***************************************************************************)
(* Aliases for the inherited initial predicate and next-state action.     *)
(***************************************************************************)
Init == HCini

Next == HCnxt

(***************************************************************************)
(* The live specification: the base hour clock plus weak fairness on the   *)
(* tick action, so a tick is never postponed forever.                      *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* The clock ticks infinitely often.
AlwaysTick == []<><<HCnxt>>_hr

\* Every hour from 1 to 12 is visited infinitely often.
AllTimes == \A n \in 1..12 : []<>(hr = n)

\* The type invariant HCini holds in every reachable state.
TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance
==============================================================================