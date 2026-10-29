---------------------------- MODULE APHourClock ----------------------------
(***************************************************************************)
(* Apalache type annotations for the HourClock specification.             *)
(*                                                                         *)
(* The original wrapper uses INSTANCE HourClock so that HourClock.tla     *)
(* does not need to be modified. This version defines the same operators  *)
(* (HCini, HCnxt, HC) inline, so the module parses on its own without     *)
(* HourClock.tla being present.                                           *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

\* Initial condition: the hour is any value from 1 to 12.
HCini == hr \in (1 .. 12)

\* Next-state action: advance the hour, wrapping 12 back to 1.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* Complete specification.
HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
THEOREM HC => []HCini
=============================================================================