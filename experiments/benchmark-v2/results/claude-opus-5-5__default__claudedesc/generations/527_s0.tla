---------------------------- MODULE Session2_MC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the "Session2" specification.                *)
(*                                                                         *)
(* The original wrapper only does EXTENDS Session2 and tells TLC to use    *)
(* Session2!Spec as the temporal specification. The contents of Session2   *)
(* are not given, and SANY cannot parse a module whose base module is      *)
(* missing. This module therefore includes a minimal stand-in for          *)
(* Session2's content, so that it is self-contained. The stand-in is a     *)
(* generic session lifecycle and is NOT recovered from the real Session2.  *)
(*                                                                         *)
(* The description mentions no fairness conditions or liveness            *)
(* properties, so none are included.                                       *)
(*                                                                         *)
(* Corresponding TLC configuration (Session2_MC.cfg):                      *)
(*     SPECIFICATION Spec                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Clients          \* set of participants that may hold sessions

VARIABLES session          \* session[c] : lifecycle state of client c

vars == << session >>

States == { "idle", "open", "closed" }

---------------------------------------------------------------------------
(* Type invariant *)
TypeOK == session \in [Clients -> States]

---------------------------------------------------------------------------
(* Initial state: every client starts without a session *)
Init == session = [c \in Clients |-> "idle"]

(* A client opens a session *)
Open(c) ==
    /\ session[c] = "idle"
    /\ session' = [session EXCEPT ![c] = "open"]

(* A client closes its open session *)
Close(c) ==
    /\ session[c] = "open"
    /\ session' = [session EXCEPT ![c] = "closed"]

(* A closed session is reset so the client can start a new one *)
Reset(c) ==
    /\ session[c] = "closed"
    /\ session' = [session EXCEPT ![c] = "idle"]

Next == \E c \in Clients : Open(c) \/ Close(c) \/ Reset(c)

---------------------------------------------------------------------------
(* The temporal specification that the model checker is configured to use *)
Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================