---------------------------- MODULE MC_HourClock2 ----------------------------
(***************************************************************************)
(* A thin wrapper that adds Apalache type annotations to HourClock2.tla    *)
(* via INSTANCE, keeping the original specification separate.              *)
(*                                                                         *)
(* HourClock2 is an alternative formulation of HourClock that uses         *)
(*     hr' = (hr % 12) + 1                                                 *)
(* instead of an IF-THEN-ELSE to advance the hour.                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock2

(***************************************************************************)
(* The behavior below mirrors HourClock2. It is restated here so the       *)
(* wrapper exposes standard entry points for model checking.               *)
(***************************************************************************)
Init == hr \in 1..12

Next == hr' = (hr % 12) + 1

Spec == Init /\ [][Next]_hr

(***************************************************************************)
(* Safety invariant: the hour always lies in 1..12.                        *)
(***************************************************************************)
HrTypeOK == hr \in 1..12

THEOREM Spec => []HrTypeOK
=============================================================================