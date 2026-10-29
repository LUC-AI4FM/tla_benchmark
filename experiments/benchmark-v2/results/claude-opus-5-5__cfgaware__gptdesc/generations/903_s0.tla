------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for the Channel module of Specifying Systems. *)
(* The Channel specification is reproduced here so that the module is      *)
(* self-contained, together with a concrete value DataVal for Data.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLE
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    chan

\* A concrete value for Data, used for model checking
DataVal == { "1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM" }

-----------------------------------------------------------------------------
(* Channel specification *)

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