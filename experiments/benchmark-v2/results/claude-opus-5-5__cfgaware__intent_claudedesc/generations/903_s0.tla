------------------------------ MODULE Channel ------------------------------
(***************************************************************************)
(* An asynchronous communication channel using a two-phase                 *)
(* ready/acknowledge handshake protocol.                                   *)
(*                                                                         *)
(* The channel state is a record with three fields:                        *)
(*   val : the data value currently on the channel                         *)
(*   rdy : the ready bit, flipped by the sender when new data is placed    *)
(*   ack : the acknowledge bit, flipped by the receiver when data is read  *)
(*                                                                         *)
(* New data is waiting to be received exactly when rdy # ack.  The sender  *)
(* may only send when rdy = ack, so it never overwrites unacknowledged     *)
(* data.  The receiver may only receive when rdy # ack, so it never        *)
(* re-reads data it has already acknowledged.  Each value that is sent is  *)
(* therefore received exactly once.                                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

(***************************************************************************)
(* A default data domain.  A model can use it to instantiate Data, for     *)
(* example with  Data <- DataVal.                                          *)
(***************************************************************************)
DataVal == {0, 1}

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

(***************************************************************************)
(* Initially the channel holds an arbitrary value and no data is pending.  *)
(***************************************************************************)
Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

(***************************************************************************)
(* The sender places data d on the channel.  It is enabled only when the   *)
(* previously sent value has been acknowledged.                            *)
(***************************************************************************)
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

(***************************************************************************)
(* The receiver reads the pending value and acknowledges it.  It is        *)
(* enabled only when there is unacknowledged data on the channel.          *)
(***************************************************************************)
Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
(***************************************************************************)
(* Derived properties                                                      *)
(***************************************************************************)

\* Data is pending exactly when the handshake bits differ.
Pending == chan.rdy # chan.ack

\* While data is pending, its value is not changed (no data loss).
NoOverwrite == [][Pending => chan'.val = chan.val]_chan

\* The handshake bits alternate: each step flips exactly one of them.
ProperSequencing ==
    [][ \/ /\ chan.rdy = chan.ack
           /\ chan'.rdy # chan.rdy
           /\ chan'.ack = chan.ack
        \/ /\ chan.rdy # chan.ack
           /\ chan'.ack # chan.ack
           /\ chan'.rdy = chan.rdy
           /\ chan'.val = chan.val ]_chan

THEOREM Spec => []TypeInvariant
=============================================================================