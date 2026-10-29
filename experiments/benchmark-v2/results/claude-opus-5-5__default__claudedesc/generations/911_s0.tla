---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == hr

-----------------------------------------------------------------------------
(* Initial condition: the hour is a value between 1 and 12 inclusive. *)
HCini == hr \in (1 .. 12)

(* Next-state relation: advance by one hour, wrapping 12 around to 1. *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(* Temporal specification: initial condition and every step is either an
   HCnxt step or a stuttering step that leaves hr unchanged.
   No fairness conditions, so the clock may stutter forever. *)
HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(* Standard names *)
Init == HCini

Next == HCnxt

Spec == HC

-----------------------------------------------------------------------------
(* Safety invariant: the hour always stays within 1 .. 12. *)
TypeInvariant == HCini

THEOREM HC => []HCini
=============================================================================