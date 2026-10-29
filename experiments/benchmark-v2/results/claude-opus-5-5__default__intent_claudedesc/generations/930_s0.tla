---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

(* Valid-hour condition: the hour is always between 1 and 12 inclusive *)
HCini == hr \in (1 .. 12)

(* Initial state: any valid hour *)
Init == HCini

(* A tick advances the hour by one, wrapping from 12 back to 1 *)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

Next == HCnxt

(* The clock formula: initial condition, then ticks or stuttering steps *)
HC == HCini /\ [][HCnxt]_hr

Spec == HC

(* Safety invariant: the hour value remains in range 1..12 *)
TypeOK == HCini

THEOREM HC => []HCini

(***************************************************************************
  Model checker configuration (HourClock.cfg):

    SPECIFICATION HC
    INVARIANT HCini
 ***************************************************************************)
=============================================================================