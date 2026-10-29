------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the Channel module of "Specifying Systems". *)
(* The Channel definitions are inlined here so that this module is        *)
(* self-contained and parses with SANY on its own.                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Set(DATUM);
    Data

VARIABLES
    \* @type: [val: DATUM, rdy: Int, ack: Int];
    chan

(***************************************************************************)
(* Concrete value for Data, used when model checking.                      *)
(***************************************************************************)
\* @type: Set(DATUM);
DataVal == { "a_OF_DATUM", "b_OF_DATUM", "c_OF_DATUM" }

(***************************************************************************)
(* Channel specification (Chapter 3 of Specifying Systems).                *)
(***************************************************************************)
TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================