------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for the Channel module of "Specifying         *)
(* Systems".  The Channel specification is reproduced inline so that the   *)
(* module is self-contained and parses with SANY without needing a         *)
(* separate Channel.tla.  DataVal gives a concrete value for the constant  *)
(* Data for model checking.                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Set(DATUM);
    Data

VARIABLES
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    chan

vars == << chan >>

(***************************************************************************)
(* Concrete value for Data, using Apalache's uninterpreted-type literals.  *)
(***************************************************************************)
DataVal == { "1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM" }

(***************************************************************************)
(* The Channel specification.                                               *)
(***************************************************************************)
TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]
    /\ chan.ack = chan.rdy

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================