---------------------------- MODULE TimerClock ----------------------------
EXTENDS Reals

(***************************************************************************)
(* Nested hour-clock module.  It is instantiated below, and its variable   *)
(* hr is substituted implicitly by the outer variable of the same name.    *)
(***************************************************************************)
---------------------------- MODULE HourClock -----------------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in 1..12
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC    == HCini /\ [][HCnxt]_hr
===========================================================================