---------------------------- MODULE AsynchChannel ----------------------------
(***************************************************************************)
(* An unreliable asynchronous single-slot channel with a two-way          *)
(* handshake for one-way data transfer.  The single shared cell `chan`    *)
(* holds one data value (val) and two one-bit control signals:            *)
(*   rdy - toggled by the sender when it places a new value in the cell   *)
(*   ack - toggled by the receiver when it has read the value             *)
(* The channel is ready for a new message iff rdy = ack.  A message is    *)
(* pending iff rdy # ack.                                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

vars == chan

-----------------------------------------------------------------------------
(* Type correctness: control bits are always bits (booleans as 0/1). *)
TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

(* Channel status predicates *)
Ready   == chan.rdy = chan.ack
Pending == chan.rdy # chan.ack

-----------------------------------------------------------------------------
(* Initially the control bits are synchronized: no outstanding message. *)
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

(* The sender writes a value d and toggles rdy, only when the channel is ready. *)
Send(d) == /\ Ready
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

(* The receiver detects a mismatch, reads val (leaving it unchanged), and   *)
(* toggles ack to signal receipt.                                           *)
Rcv == /\ Pending
       /\ chan' = [chan EXCEPT !.ack = 1 - @]

SendSome == \E d \in Data : Send(d)

Next == SendSome \/ Rcv

(* Arbitrary interleaving of sender and receiver steps; the receiver is     *)
(* weakly fair so pending messages are eventually acknowledged.             *)
Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Rcv)

-----------------------------------------------------------------------------
(* Safety properties *)

(* The sender only changes rdy when the channel is ready. *)
SendOnlyWhenAllowed ==
    [][chan'.rdy # chan.rdy => chan.rdy = chan.ack]_vars

(* The receiver only toggles ack when a message has been detected. *)
RcvOnlyOnMessage ==
    [][chan'.ack # chan.ack => chan.rdy # chan.ack]_vars

(* A pending (unacknowledged) value is never overwritten or corrupted. *)
DataPreserved ==
    [][Pending => chan'.val = chan.val]_vars

(* Data may change only together with a send (rdy toggle). *)
DataOnlyChangedBySend ==
    [][chan'.val # chan.val => (Ready /\ chan'.rdy # chan.rdy)]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

(* If the sender has sent a fixed value d, the receiver eventually         *)
(* acknowledges it (with d still intact up to the acknowledgement).        *)
SentIsAcked ==
    \A d \in Data : (Pending /\ chan.val = d) ~> (Ready /\ chan.val = d)

(* The receiver does not starve: whenever a message is pending, it is      *)
(* eventually acknowledged; hence the channel is infinitely often ready.   *)
NoStarvation == Pending ~> Ready

InfinitelyOftenReady == []<>Ready

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => SendOnlyWhenAllowed /\ RcvOnlyOnMessage /\ DataPreserved
THEOREM Spec => SentIsAcked /\ NoStarvation
=============================================================================