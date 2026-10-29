---------------------------- MODULE APLiveHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper for the LiveHourClock specification.  The only   *)
(* purpose of this module is to give Apalache a type for the variable hr. *)
(* The definitions of LiveHourClock (and the HourClock it extends) are     *)
(* reproduced inline, with hr substituted for the original variable, so   *)
(* that the module is self-contained and binds to the model configuration. *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

(***************************************************************************)
(* HourClock definitions                                                   *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* LiveHourClock definitions                                               *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1 .. 12 : []<>(hr = n)

TypeOK == hr \in (1 .. 12)

-----------------------------------------------------------------------------
THEOREM HC => []HCini
THEOREM LSpec => AlwaysTick /\ AllTimes
=============================================================================