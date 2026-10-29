---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the MultiUser specification.                 *)
(* MultiUser (users sharing one resource) is given inline here, so the     *)
(* module is self-contained and parses with SANY. The wrapper defines      *)
(* const_17385913267612000 == 1..2 as the value of the Users parameter.    *)
(* It also collects several properties. Each one says the MultiUser spec   *)
(* implements a single user's view, given by an instance of SingleUser.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

-------------------------- MODULE SingleUser --------------------------
(* The behavior of one user, seen in isolation. *)
VARIABLE st

SUInit    == st = "idle"
SURequest == st = "idle"    /\ st' = "waiting"
SUAcquire == st = "waiting" /\ st' = "using"
SURelease == st = "using"   /\ st' = "idle"
SUNext    == SURequest \/ SUAcquire \/ SURelease

Spec == SUInit /\ [][SUNext]_st /\ WF_st(SURelease)
========================================================================