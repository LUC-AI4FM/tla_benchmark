------------------------------ MODULE AsyncInterface ------------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val,      \* the data channel
          rdy,      \* the sender's one-bit ready line
          ack,      \* the receiver's one-bit acknowledge line
          received  \* auxiliary: last value consumed by the receiver

vars == <<val, rdy, ack, received>>

-----------------------------------------------------------------------------------
TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}
    /\ received \in Data

-----------------------------------------------------------------------------------
Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy
    /\ received = val

\* Sender: when the previous value was consumed (rdy = ack), present a new
\* arbitrary value and toggle the ready line.
Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ UNCHANGED <<ack, received>>

\* Receiver: when a change is detected (rdy # ack), consume the value and
\* toggle the acknowledge line.
Rcv ==
    /\ rdy # ack
    /\ received' = val
    /\ ack' = 1 - ack
    /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Fairness == WF_vars(Rcv) /\ WF_vars(Send)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------
\* Pending vs. consumed: the handshake bits alternate correctly.
Pending  == rdy # ack
Consumed == rdy = ack

HandshakeInvariant ==
    /\ Pending \/ Consumed
    /\ Consumed => received = val

\* Data integrity: the receiver only ever consumes exactly the value the
\* sender presented, and the data is not altered while a transfer is pending.
DataIntegrity == Consumed => received = val

ValStableWhilePending ==
    [][Pending => (val' = val)]_vars

DeliveredCorrectly ==
    [][Rcv => received' = val]_vars

\* Deadlock freedom: some action is always enabled.
NoDeadlock == ENABLED Send \/ ENABLED Rcv

\* Liveness: every send is eventually acknowledged.
EventualAck == Pending ~> Consumed

\* Repeated transfers happen infinitely often.
RepeatedTransfers == []<>Pending /\ []<>Consumed

-----------------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []HandshakeInvariant
THEOREM Spec => []DataIntegrity
THEOREM Spec => []NoDeadlock
THEOREM Spec => ValStableWhilePending
THEOREM Spec => DeliveredCorrectly
THEOREM Spec => EventualAck
====================================================================================