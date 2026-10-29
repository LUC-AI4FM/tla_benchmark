--------------------------- MODULE LiveHourClock ---------------------------
(***************************************************************************)
(* A live 12-hour clock. The base hour-clock definitions (HCini, HCnxt,    *)
(* HC) are given inline in the "Base hour clock" section so that the       *)
(* module parses on its own. In a two-file setup, that section would be    *)
(* the separate module HourClock, and this module would EXTENDS it.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS MinHour, MaxHour

ASSUME HourBounds == /\ MinHour = 1
                     /\ MaxHour = 12

VARIABLE hr

vars == <<hr>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Base hour clock                                                         *)
(***************************************************************************)

HCini == hr \in (MinHour .. MaxHour)

HCnxt == hr' = IF hr # MaxHour THEN hr + 1 ELSE MinHour

HC == HCini /\ [][HCnxt]_hr

---------------------------------------------------------------------------
(***************************************************************************)
(* Live hour clock                                                         *)
(***************************************************************************)

Init == HCini

Next == HCnxt

\* Weak fairness on the tick action ensures that the clock never stops.
LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

---------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Safety invariant: hr always stays within 1..12.
TypeOK == hr \in (MinHour .. MaxHour)

\* Property 1: ticking actions occur infinitely often.
AlwaysTick == []<><<HCnxt>>_hr

\* Property 2: every hour from 1 to 12 is visited infinitely often.
AllTimes == \A n \in (MinHour .. MaxHour) : []<>(hr = n)

\* Property 3: the hour always remains in the valid range.
TypeInvariance == []HCini

THEOREM LiveTheorem == LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

THEOREM SafetyTheorem == Spec => []TypeOK
=============================================================================