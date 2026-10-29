---------------------------- MODULE MC_HourClock2 ----------------------------
(***************************************************************************)
(* Apalache type annotations for the hour clock.                           *)
(*                                                                         *)
(* The original wrapper applies annotations to HourClock2.tla via          *)
(* INSTANCE. HourClock2 is an alternative formulation of HourClock that    *)
(* uses (hr % 12) + 1 instead of an IF-THEN-ELSE.                          *)
(*                                                                         *)
(* This module defines the HourClock2 operators inline, so it parses as a  *)
(* standalone file. The wrapper would otherwise contain only:              *)
(*                                                                         *)
(*     INSTANCE HourClock2                                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

(* Contents of HourClock2 *)
HCini  == hr \in (1 .. 12)

HCnxt2 == hr' = (hr % 12) + 1

HC2    == HCini /\ [][HCnxt2]_hr

=============================================================================