---------------------------- MODULE MC_MultiUser ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the MultiUser specification.                 *)
(*                                                                         *)
(* The MultiUser system is a set of users competing for one critical       *)
(* resource. The SingleUser module describes the behavior of one user      *)
(* seen in isolation. It is instantiated for specific users (SingleUser2,  *)
(* SingleUser3, SingleUserP(p)). Its Spec formulas are the refinement      *)
(* properties that TLC checks against the multi-user Spec.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

------------------------------ MODULE SingleUser ------------------------------
(***************************************************************************)
(* Abstract behavior of a single user `me': it cycles through              *)
(* idle -> waiting -> critical -> idle.                                    *)
(***************************************************************************)
CONSTANT me
VARIABLE st

SStates == {"idle", "waiting", "critical"}

STypeOK == st \in SStates

SInit == st = "idle"

SRequest == st = "idle"     /\ st' = "waiting"
SEnter   == st = "waiting"  /\ st' = "critical"
SExit    == st = "critical" /\ st' = "idle"

SNext == SRequest \/ SEnter \/ SExit

Spec == SInit /\ [][SNext]_st
===============================================================================