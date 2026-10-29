---------------------------- MODULE APLiveHourClock ----------------------------
(***************************************************************************)
(* A type-annotated wrapper for the LiveHourClock specification.  It       *)
(* declares the variable hr with an Apalache type annotation and           *)
(* instantiates LiveHourClock, substituting its own hr for the hr of       *)
(* LiveHourClock (implicit substitution hr <- hr).                         *)
(*                                                                         *)
(* The original wrapper defines no operators. Init, Next and Spec below    *)
(* are only aliases to the definitions imported from                       *)
(* LiveHourClock/HourClock, so the module exposes the standard entry       *)
(* points.                                                                 *)
(***************************************************************************)

VARIABLES
    \* @type: Int;
    hr

INSTANCE LiveHourClock

-----------------------------------------------------------------------------
(* Aliases to the instantiated definitions. *)

Init == HCini

Next == HCnxt

vars == hr

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: the clock always shows an hour between 1 and 12. *)
TypeOK == hr \in 1..12

(* Liveness: the clock keeps ticking forever. *)
Ticks == []<><<Next>>_vars

(* Liveness: every hour is displayed infinitely often. *)
EveryHour == \A n \in 1..12 : []<>(hr = n)

THEOREM Spec => []TypeOK
THEOREM Spec => Ticks
THEOREM Spec => EveryHour
=============================================================================