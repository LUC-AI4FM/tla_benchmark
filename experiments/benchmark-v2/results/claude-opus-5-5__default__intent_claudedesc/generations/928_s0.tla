---------------------------- MODULE HourClock2 ----------------------------
(***************************************************************************)
(* An alternative formulation of the 12-hour clock from module HourClock. *)
(* HourClock defines:                                                     *)
(*   VARIABLE hr                                                          *)
(*   HCini == hr \in (1 .. 12)                                            *)
(*   HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1                         *)
(*   HC    == HCini /\ [][HCnxt]_hr                                       *)
(***************************************************************************)
EXTENDS HourClock

(***************************************************************************)
(* Alternative next-state relation using modular arithmetic.              *)
(***************************************************************************)
HCnxt2 == hr' = (hr % 12) + 1

(***************************************************************************)
(* Alternative specification built from the shared initial condition.     *)
(***************************************************************************)
HC2 == HCini /\ [][HCnxt2]_hr

(***************************************************************************)
(* Generic names for the primary formulation.                             *)
(***************************************************************************)
Init == HCini
Next == HCnxt
Spec == HC

(***************************************************************************)
(* Type invariant shared by both formulations.                            *)
(***************************************************************************)
TypeOK == hr \in 1 .. 12

(***************************************************************************)
(* The two specifications are equivalent: each implies the other.         *)
(***************************************************************************)
THEOREM HC <=> HC2

THEOREM HC => []TypeOK
THEOREM HC2 => []TypeOK

(***************************************************************************)
(* Model checker configuration (HourClock2.cfg):                          *)
(*                                                                         *)
(*   SPECIFICATION HC                                                      *)
(*   INVARIANT TypeOK                                                      *)
(*   PROPERTY HC2                                                          *)
(*                                                                         *)
(* To check the converse direction, use SPECIFICATION HC2 and PROPERTY HC.*)
(***************************************************************************)
=============================================================================