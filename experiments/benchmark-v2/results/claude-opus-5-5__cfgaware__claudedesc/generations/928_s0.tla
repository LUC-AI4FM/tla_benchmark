----------------------------- MODULE HourClock2 -----------------------------
(***************************************************************************)
(* An alternative but equivalent formulation of the 12-hour clock.        *)
(* The base HourClock definitions are included inline so the module is    *)
(* self-contained.                                                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE hr

(***************************************************************************)
(* Definitions from the base HourClock module.                             *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Alternative next-state relation and specification.                      *)
(***************************************************************************)
HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

THEOREM HC <=> HC2
=============================================================================