---------------------------- MODULE HourClock2 ----------------------------
(***************************************************************************)
(* An alternative but equivalent formulation of the 12-hour clock          *)
(* specification from module HourClock.                                    *)
(*                                                                         *)
(* From HourClock this module inherits:                                    *)
(*   VARIABLE hr                                                           *)
(*   HCini == hr \in (1 .. 12)                                             *)
(*   HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1                          *)
(*   HC    == HCini /\ [][HCnxt]_hr                                        *)
(* and the arithmetic operators of Naturals.                               *)
(***************************************************************************)
EXTENDS HourClock

(***************************************************************************)
(* Alternative next-state relation: take the modulus, then add one.        *)
(***************************************************************************)
HCnxt2 == hr' = (hr % 12) + 1

(***************************************************************************)
(* The alternative full specification.                                     *)
(***************************************************************************)
HC2 == HCini /\ [][HCnxt2]_hr

(***************************************************************************)
(* Safety invariant: the hour always stays in 1..12.                       *)
(***************************************************************************)
TypeOK == hr \in 1 .. 12

THEOREM HC2 => []TypeOK

(***************************************************************************)
(* The two formulations describe exactly the same set of behaviors.        *)
(***************************************************************************)
THEOREM HC <=> HC2

(***************************************************************************)
(* Model-checking configuration (HourClock2.cfg):                          *)
(*   SPECIFICATION HC                                                      *)
(*   PROPERTY HC2                                                          *)
(* This checks the direction HC => HC2 of the equivalence theorem.         *)
(***************************************************************************)
=============================================================================