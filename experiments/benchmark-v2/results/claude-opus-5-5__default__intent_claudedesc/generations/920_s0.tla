---------------------------- MODULE AsyncChannel ----------------------------
(***************************************************************************)
(* A simple asynchronous communication channel using a two-phase          *)
(* handshaking protocol. The sender places a value on the channel and     *)
(* toggles the rdy bit. The receiver acknowledges by toggling the ack bit. *)
(* Data is pending exactly when rdy # ack.                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

vars == << chan >>

-----------------------------------------------------------------------------
(* Type safety *)
TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

-----------------------------------------------------------------------------
(* Initial state: idle / synchronized, no data pending *)
Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

(* Sender places a new value d on the channel when the previous one *)
(* has been acknowledged.                                           *)
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

(* Receiver acknowledges receipt when new unacknowledged data is waiting. *)
Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

(* No progress is required, so no fairness condition is included. *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Correctness properties *)

(* Data is pending exactly when the signal bits differ. *)
Pending == chan.rdy # chan.ack

(* A send may only happen when no data is pending, and it makes data pending. *)
SendOnlyWhenIdle ==
    [][(chan'.rdy # chan.rdy) => (~Pending /\ chan'.rdy # chan'.ack)]_vars

(* A receive may only happen when data is pending, and it clears the pending data. *)
RcvOnlyWhenPending ==
    [][(chan'.ack # chan.ack) => (Pending /\ chan'.rdy = chan'.ack)]_vars

(* While a value is pending, it cannot be overwritten. This means no data *)
(* is lost.                                                               *)
NoOverwrite ==
    [][Pending => (chan'.val = chan.val)]_vars

(* Each step toggles exactly one of the two signal bits. Sends and receives *)
(* therefore alternate strictly, so each value is received exactly once.   *)
StrictAlternation ==
    [][ \/ (chan'.rdy # chan.rdy /\ chan'.ack = chan.ack)
        \/ (chan'.ack # chan.ack /\ chan'.rdy = chan.rdy) ]_vars

NoLossNoDuplication ==
    SendOnlyWhenIdle /\ RcvOnlyWhenPending /\ NoOverwrite /\ StrictAlternation

(* The protocol logic never deadlocks. Some action is always enabled, *)
(* provided Data is nonempty.                                         *)
DeadlockFree == ENABLED Next

THEOREM Spec => []TypeInvariant
THEOREM Spec => NoLossNoDuplication
=============================================================================