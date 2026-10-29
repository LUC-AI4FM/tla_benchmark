---------------------------- MODULE APHourClock2 ----------------------------
(***************************************************************************)
(* Thin wrapper that adds Apalache type annotations to HourClock2.tla      *)
(* through INSTANCE, so the original specification stays separate.         *)
(*                                                                         *)
(* HourClock2 is another way to write HourClock. Its next-state action     *)
(* uses (hr % 12) + 1 in place of an IF-THEN-ELSE:                         *)
(*                                                                         *)
(*     HCini == hr \in (1 .. 12)                                           *)
(*     HCnxt == hr' = (hr % 12) + 1                                        *)
(*     HC    == HCini /\ [][HCnxt]_hr                                      *)
(*                                                                         *)
(* The INSTANCE below imports all of these definitions unchanged.          *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

INSTANCE HourClock2

(***************************************************************************)
(* The wrapper has no behavior of its own. The names below only alias the *)
(* operators imported from HourClock2, using the standard names a model   *)
(* checker expects.                                                       *)
(***************************************************************************)
Init == HCini

Next == HCnxt

Spec == HC

\* Safety invariant from HourClock2 (THEOREM HC => []HCini)
TypeOK == HCini

=============================================================================