---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

(***************************************************************************)
(* Initial condition: the hour is some value in 1..12.                     *)
(***************************************************************************)
HCini == hr \in 1..12

(***************************************************************************)
(* Single-step transition: advance the hour by one, wrapping 12 to 1.      *)
(***************************************************************************)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

(***************************************************************************)
(* Safety specification.                                                   *)
(***************************************************************************)
HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Liveness specification: weak fairness on the advancing step, so the     *)
(* clock cannot stop ticking forever.                                      *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

(***************************************************************************)
(* Properties to be checked.                                               *)
(***************************************************************************)
\* (2) Infinitely many advancing steps occur.
AlwaysTick == []<><<HCnxt>>_hr

\* (3) Every hour value occurs infinitely often.
AllTimes == \A n \in 1..12 : []<>(hr = n)

\* (1) The hour always stays in 1..12.
TypeInvariance == []HCini

THEOREM LSpec => TypeInvariance
THEOREM LSpec => AlwaysTick
THEOREM LSpec => AllTimes
=============================================================================