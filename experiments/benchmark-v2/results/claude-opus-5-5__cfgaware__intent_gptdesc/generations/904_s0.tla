---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

(* Initial condition: hour is in the 12-hour range 1..12 *)
HCini == hr \in (1 .. 12)

(* External increment event: advance by one, wrapping 12 -> 1 *)
Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HCnxt == Tick

(* Stuttering is allowed through [][HCnxt]_hr.
   Weak fairness means the increment keeps occurring eventually.
   It is not required on every step. *)
HC == HCini /\ [][HCnxt]_hr /\ WF_hr(HCnxt)

(* Safety specification without fairness *)
HCSafe == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(* Correctness properties *)

(* (1) Invariant: hour always within cyclic range *)
TypeOK == hr \in (1 .. 12)

(* (2) Functional correctness of increment with wrap-around *)
WrapCorrect ==
    [][ hr' # hr =>
          ( (hr = 12 => hr' = 1)
         /\ (hr # 12 => hr' = hr + 1) ) ]_hr

(* (3) Liveness: if increments occur infinitely often, every hour value
   is visited infinitely often *)
IncInfinitelyOften == []<><<HCnxt>>_hr

Recurrent == \A h \in (1 .. 12) : []<>(hr = h)

Liveness == IncInfinitelyOften => Recurrent

THEOREM HC => []HCini
THEOREM HC => []TypeOK
THEOREM HC => WrapCorrect
THEOREM HC => Liveness
=============================================================================