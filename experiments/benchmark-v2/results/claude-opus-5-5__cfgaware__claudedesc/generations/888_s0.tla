------------------------- MODULE ApaAsynchInterface -------------------------
(***************************************************************************)
(* Apalache-annotated version of the asynchronous interface specification. *)
(* The base AsynchInterface definitions are reproduced inline so that the *)
(* module is self-contained and parses on its own.                         *)
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

\* Concrete two-element set of symbolic datum values for model checking
DataVal == { "0_OF_DATUM", "1_OF_DATUM" }

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

THEOREM Spec => []TypeInvariant
=============================================================================