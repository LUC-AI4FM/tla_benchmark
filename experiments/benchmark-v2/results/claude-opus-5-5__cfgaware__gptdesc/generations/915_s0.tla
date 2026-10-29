------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for the FIFO Channel specification.          *)
(* The Channel definitions are included here so that this module is       *)
(* self-contained; they correspond to the Channel module that this        *)
(* wrapper would otherwise instantiate.                                   *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Str);
    Data

VARIABLE
    \* @type: { val: Str, rdy: Int, ack: Int };
    chan

\* A concrete value for the Data constant, for use in model checking.
DataVal == { "a", "b", "c" }

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