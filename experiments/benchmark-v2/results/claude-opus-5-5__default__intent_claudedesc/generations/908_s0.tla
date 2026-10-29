------------------------------ MODULE AsyncChannel ------------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

vars == << chan >>

-----------------------------------------------------------------------------
(* Type safety *)

TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

-----------------------------------------------------------------------------
(* Helper predicates for the toggle-based handshake *)

Idle    == chan.rdy = chan.ack
Pending == chan.rdy # chan.ack

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

-----------------------------------------------------------------------------
(* Actions *)

Send(d) ==
    /\ Idle
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ Pending
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Rcv) /\ WF_vars(\E d \in Data : Send(d))

-----------------------------------------------------------------------------
(* Safety properties *)

\* The channel is always either idle or holding exactly one pending message.
HandshakeInvariant == Idle \/ Pending

\* No spurious sends: the ready bit toggles only when the channel was idle.
NoSpuriousSend ==
    [][ (chan'.rdy # chan.rdy) => (chan.rdy = chan.ack) ]_vars

\* No spurious receives: the ack bit toggles only when data was pending.
NoSpuriousRcv ==
    [][ (chan'.ack # chan.ack) => (chan.rdy # chan.ack) ]_vars

\* No data loss: the value cannot be overwritten while it is still pending.
NoDataLoss ==
    [][ Pending => (chan'.val = chan.val) ]_vars

\* Strict alternation: sends and receives never happen in the same step,
\* so each sent message is acknowledged exactly once before the next send.
StrictAlternation ==
    [][ ~((chan'.rdy # chan.rdy) /\ (chan'.ack # chan.ack)) ]_vars

\* No duplication: an acknowledgment always returns the channel to idle.
NoDuplication ==
    [][ (chan'.ack # chan.ack) => (chan'.rdy = chan'.ack) ]_vars

-----------------------------------------------------------------------------
(* Liveness property (holds under FairSpec) *)

\* Every pending message is eventually acknowledged.
EventualDelivery == Pending ~> Idle

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []HandshakeInvariant
THEOREM Spec => NoSpuriousSend /\ NoSpuriousRcv
THEOREM Spec => NoDataLoss /\ StrictAlternation /\ NoDuplication
THEOREM FairSpec => EventualDelivery
=============================================================================