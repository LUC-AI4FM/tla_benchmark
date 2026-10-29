------------------------------ MODULE MC_Channel ------------------------------
(***************************************************************************)
(* Typed wrapper around the asynchronous Channel specification, with       *)
(* Apalache type annotations. The original Channel module (Lamport,        *)
(* "Specifying Systems") is normally imported with                         *)
(*                                                                         *)
(*     INSTANCE Channel                                                    *)
(*                                                                         *)
(* Its definitions are reproduced here unchanged so that this module is    *)
(* self-contained and passes SANY without needing a separate Channel.tla.  *)
(* The semantics are identical to the instantiated module.                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLE
    \* @type: [val: DATUM, rdy: Int, ack: Int];
    chan

\* Concrete instantiation of the constant for model checking (Apalache ConstInit).
ConstInit == Data = {"d1_OF_DATUM", "d2_OF_DATUM"}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Definitions of the Channel module (equivalent to INSTANCE Channel).     *)
(***************************************************************************)

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

\* The sender puts value d on the channel and toggles rdy.
Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* The receiver takes the value and acknowledges by toggling ack.
Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================