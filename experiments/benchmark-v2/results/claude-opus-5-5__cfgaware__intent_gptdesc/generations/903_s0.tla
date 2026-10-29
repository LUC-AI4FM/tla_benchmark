---------------------------- MODULE AsynchChannel ----------------------------
EXTENDS Naturals

CONSTANT Data

NoData == CHOOSE v : v \notin Data

DataVal == Data \cup {NoData}

VARIABLES chan,      \* contents of the channel: a datum or NoData
          rdy,       \* sender's handshake bit (toggled on each send)
          ack,       \* receiver's handshake bit (toggled on each receive)
          sndRdy,    \* sender indicates it is ready to send
          rcvRdy,    \* receiver indicates it is ready to accept
          lastSent,  \* ghost: last datum placed in the channel
          lastRcvd   \* ghost: last datum consumed by the receiver

vars == <<chan, rdy, ack, sndRdy, rcvRdy, lastSent, lastRcvd>>

TypeInvariant ==
  /\ chan \in DataVal
  /\ rdy \in {0, 1}
  /\ ack \in {0, 1}
  /\ sndRdy \in BOOLEAN
  /\ rcvRdy \in BOOLEAN
  /\ lastSent \in DataVal
  /\ lastRcvd \in DataVal

Init ==
  /\ chan = NoData
  /\ rdy = 0
  /\ ack = 0
  /\ sndRdy \in BOOLEAN
  /\ rcvRdy \in BOOLEAN
  /\ lastSent = NoData
  /\ lastRcvd = NoData

\* Sender may detect that the receiver acknowledged the last datum
Acked == rdy = ack

\* Receiver may detect that a fresh datum is present
Fresh == rdy # ack /\ chan # NoData

SenderBecomeReady ==
  /\ ~sndRdy
  /\ sndRdy' = TRUE
  /\ UNCHANGED <<chan, rdy, ack, rcvRdy, lastSent, lastRcvd>>

SenderBecomeIdle ==
  /\ sndRdy
  /\ sndRdy' = FALSE
  /\ UNCHANGED <<chan, rdy, ack, rcvRdy, lastSent, lastRcvd>>

Send(d) ==
  /\ sndRdy
  /\ Acked
  /\ chan = NoData
  /\ chan' = d
  /\ rdy' = 1 - rdy
  /\ sndRdy' = FALSE
  /\ lastSent' = d
  /\ UNCHANGED <<ack, rcvRdy, lastRcvd>>

ReceiverBecomeReady ==
  /\ ~rcvRdy
  /\ rcvRdy' = TRUE
  /\ UNCHANGED <<chan, rdy, ack, sndRdy, lastSent, lastRcvd>>

ReceiverBecomeIdle ==
  /\ rcvRdy
  /\ rcvRdy' = FALSE
  /\ UNCHANGED <<chan, rdy, ack, sndRdy, lastSent, lastRcvd>>

Rcv ==
  /\ rcvRdy
  /\ Fresh
  /\ lastRcvd' = chan
  /\ chan' = NoData
  /\ ack' = 1 - ack
  /\ UNCHANGED <<rdy, sndRdy, rcvRdy, lastSent>>

\* Receiver attempts to receive and observes the channel is empty
ObserveEmpty ==
  /\ rcvRdy
  /\ ~Fresh
  /\ UNCHANGED vars

Next ==
  \/ SenderBecomeReady
  \/ SenderBecomeIdle
  \/ \E d \in Data : Send(d)
  \/ ReceiverBecomeReady
  \/ ReceiverBecomeIdle
  \/ Rcv

Fairness ==
  /\ WF_vars(Rcv)
  /\ WF_vars(\E d \in Data : Send(d))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

AtMostOneDatum == chan \in DataVal

ChannelConsistent ==
  /\ (chan # NoData) => (rdy # ack /\ chan = lastSent)
  /\ (rdy = ack) => chan = NoData

NoPhantomReceive ==
  lastRcvd # NoData => lastRcvd \in Data

AckMeansDelivered ==
  [][ (ack' # ack) => (chan # NoData /\ lastRcvd' = chan /\ chan' = NoData) ]_vars

ReceiveOnlySent ==
  [][ (lastRcvd' # lastRcvd) => lastRcvd' = lastSent ]_vars

Safety ==
  /\ TypeInvariant
  /\ AtMostOneDatum
  /\ ChannelConsistent
  /\ NoPhantomReceive

\* Liveness properties

OfferedEventuallyConsumed ==
  \A d \in Data :
    ((chan = d /\ rcvRdy) ~> (chan = NoData \/ ~rcvRdy))

ReceiverProgress ==
  []<>(rcvRdy) => []<>(~Fresh \/ ~rcvRdy)

=============================================================================