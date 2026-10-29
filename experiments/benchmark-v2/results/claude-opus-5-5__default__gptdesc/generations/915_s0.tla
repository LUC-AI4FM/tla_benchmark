-------------------------------- MODULE APChannel --------------------------------
(***************************************************************************)
(* Apalache type annotations for FIFO/Channel.tla.                         *)
(*                                                                         *)
(* This module is meant to be a typed wrapper around Channel. In a         *)
(* setting where Channel.tla is on the module path, the definitions below  *)
(* are obtained via                                                        *)
(*                                                                         *)
(*     INSTANCE Channel                                                    *)
(*                                                                         *)
(* so that the original Channel module stays free of tool-specific         *)
(* details. To keep this module self-contained and parseable on its own,   *)
(* the instantiated definitions of Channel are expanded here verbatim.     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: [val: Int, rdy: Int, ack: Int];
    chan

(***************************************************************************)
(* Definitions of Channel (equivalent to INSTANCE Channel).                *)
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

THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* A concrete value for Data, for use in model checking configurations.    *)
(***************************************************************************)
DataVal == {0, 1}

=============================================================================