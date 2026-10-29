---------------------------- MODULE MC_AsynchInterface ----------------------------
(***************************************************************************)
(* Apalache-annotated wrapper for the asynchronous handshake interface.   *)
(* The definitions of the original AsynchInterface module are included   *)
(* inline, so this module parses on its own without the base module.     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLES
    \* @type: DATUM;
    val,
    \* @type: Int;
    rdy,
    \* @type: Int;
    ack

\* Concrete instantiation of Data for model checking (Apalache ConstInit)
ConstInit == Data = { "d1_OF_DATUM", "d2_OF_DATUM" }

-----------------------------------------------------------------------------
(* Contents of AsynchInterface *)

vars == << val, rdy, ack >>

TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ UNCHANGED ack

Rcv ==
    /\ rdy # ack
    /\ ack' = 1 - ack
    /\ UNCHANGED << val, rdy >>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety property checked by the configuration *)

TypeOK == TypeInvariant

THEOREM Spec => []TypeInvariant
=============================================================================