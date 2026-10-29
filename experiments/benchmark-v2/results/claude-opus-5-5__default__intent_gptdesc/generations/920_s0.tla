---------------------------- MODULE HandshakeChannel ----------------------------
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLE chan

vars == << chan >>

-----------------------------------------------------------------------------
(* Type and range constraint on the channel state                          *)
-----------------------------------------------------------------------------

TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

-----------------------------------------------------------------------------
(* Derived predicates                                                      *)
-----------------------------------------------------------------------------

Synchronized == chan.rdy = chan.ack

Pending == chan.rdy # chan.ack

-----------------------------------------------------------------------------
(* Initial state: empty channel, well typed, sender and receiver in sync   *)
-----------------------------------------------------------------------------

Init ==
    /\ TypeInvariant
    /\ chan.rdy = chan.ack

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------

Send(d) ==
    /\ Synchronized
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ Pending
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

SendSome == \E d \in Data : Send(d)

Next == SendSome \/ Rcv

-----------------------------------------------------------------------------
(* Fairness and full specification                                         *)
-----------------------------------------------------------------------------

Fairness ==
    /\ WF_vars(SendSome)
    /\ WF_vars(Rcv)

Spec == Init /\ [][Next]_vars /\ Fairness

SafetySpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                       *)
-----------------------------------------------------------------------------

\* The sender never overwrites an unacknowledged message: while a message is
\* pending, neither the data value nor the ready bit may change.
NoOverwrite ==
    [][ Pending => (chan'.val = chan.val /\ chan'.rdy = chan.rdy) ]_vars

\* The receiver never acknowledges when there is no pending message.
NoSpuriousAck ==
    [][ (chan'.ack # chan.ack) => Pending ]_vars

\* A new message is only placed when sender and receiver are synchronized.
SendOnlyWhenSynced ==
    [][ (chan'.rdy # chan.rdy) => Synchronized ]_vars

\* Each step toggles exactly one control bit (strict alternation).
Alternation ==
    [][ \/ (chan'.rdy # chan.rdy /\ chan'.ack = chan.ack)
        \/ (chan'.ack # chan.ack /\ chan'.rdy = chan.rdy) ]_vars

Safety ==
    /\ []TypeInvariant
    /\ NoOverwrite
    /\ NoSpuriousAck
    /\ SendOnlyWhenSynced
    /\ Alternation

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)
-----------------------------------------------------------------------------

\* Every pending message is eventually acknowledged (handshake completes).
HandshakeCompletes == Pending ~> Synchronized

\* Whenever synchronized, a new message is eventually sent.
SenderProgress == Synchronized ~> Pending

\* Messages are transferred infinitely often.
EventualTransfer == []<>Pending /\ []<>Synchronized

Liveness ==
    /\ HandshakeCompletes
    /\ SenderProgress
    /\ EventualTransfer

-----------------------------------------------------------------------------
(* Theorems                                                                *)
-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant
THEOREM Spec => Safety
THEOREM Spec => Liveness

=============================================================================