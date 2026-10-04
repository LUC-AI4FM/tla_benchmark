---------------------------- MODULE HC2 ----------------------------
EXTENDS Naturals

CONSTANT HRset
ASSUME HRset = 1..12

VARIABLE hr

-----------------------------------------------------------------------------

(* Definitions inherited from HourClock module *)

HCini == hr \in HRset

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------

(* Alternative next-state action using modulo arithmetic *)

HCnxt2 == hr' = (hr % 12) + 1

(* Alternative specification using HCnxt2 *)

HC2 == HCini /\ [][HCnxt2]_hr

-----------------------------------------------------------------------------

(* Theorem asserting equivalence of HC and HC2 *)

THEOREM HC <=> HC2

=============================================================================