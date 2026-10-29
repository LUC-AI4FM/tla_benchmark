---------------------------- MODULE MC_Channel ----------------------------
(***************************************************************************)
(* Apalache-annotated wrapper for the Channel specification: a single-     *)
(* place asynchronous channel between a sender and a receiver that uses a  *)
(* two-phase handshake (rdy / ack) protocol.                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Str);
    Data

VARIABLE
    \* @type: { val: Str, rdy: Int, ack: Int };
    chan

vars == <<chan>>

(***************************************************************************)
(* Concrete constant initialization for model checking (Apalache          *)
(* --cinit=ConstInit); a two-element data set.                             *)
(***************************************************************************)
ConstInit == Data = {"d1", "d2"}

(***************************************************************************)
(* Channel specification                                                   *)
(***************************************************************************)
TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

\* Sender places data d on the channel and signals readiness
\* (only allowed when the previous value has been acknowledged).
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* Receiver reads the value and acknowledges receipt.
Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety property checked by the model checker.                           *)
(***************************************************************************)
THEOREM Spec => []TypeInvariant
=============================================================================