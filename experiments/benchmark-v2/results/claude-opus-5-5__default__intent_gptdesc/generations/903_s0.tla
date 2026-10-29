---------------------------- MODULE AsyncChannel ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data,      \* finite set of payload values
          NoData,    \* distinguished "empty" value, not in Data
          MaxMsgs    \* bound on the number of transmissions (for model checking)

ASSUME /\ NoData \notin Data
       /\ MaxMsgs \in Nat

VARIABLES chan,       \* contents of the one-place channel
          sendReady,  \* sender's ready-to-send signal
          ack,        \* acknowledgment: last transmitted datum was consumed
          recvReady,  \* receiver's ready-to-accept signal
          fresh,      \* a new, not yet consumed datum is present
          rcvStatus,  \* receiver's observation of its last attempt
          sentLog,    \* history of all data sent (auxiliary)
          recvLog     \* history of all data received (auxiliary)

vars == <<chan, sendReady, ack, recvReady, fresh, rcvStatus, sentLog, recvLog>>

RcvStatuses == {"idle", "waiting", "got", "empty"}

-----------------------------------------------------------------------------
TypeOK ==
  /\ chan \in Data \cup {NoData}
  /\ sendReady \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ recvReady \in BOOLEAN
  /\ fresh \in BOOLEAN
  /\ rcvStatus \in RcvStatuses
  /\ sentLog \in Seq(Data)
  /\ recvLog \in Seq(Data)

Init ==
  /\ chan = NoData
  /\ sendReady = FALSE
  /\ ack = TRUE
  /\ recvReady = FALSE
  /\ fresh = FALSE
  /\ rcvStatus = "idle"
  /\ sentLog = << >>
  /\ recvLog = << >>

-----------------------------------------------------------------------------
(* Sender actions *)

\* The sender raises its ready signal once the previous datum was acknowledged.
SenderBecomeReady ==
  /\ ~sendReady
  /\ ack
  /\ sendReady' = TRUE
  /\ UNCHANGED <<chan, ack, recvReady, fresh, rcvStatus, sentLog, recvLog>>

\* The sender places a datum into the (empty) channel.
Send(d) ==
  /\ sendReady
  /\ ack
  /\ chan = NoData
  /\ Len(sentLog) < MaxMsgs
  /\ chan' = d
  /\ sendReady' = FALSE
  /\ ack' = FALSE
  /\ fresh' = TRUE
  /\ sentLog' = Append(sentLog, d)
  /\ UNCHANGED <<recvReady, rcvStatus, recvLog>>

SenderStep == SenderBecomeReady \/ \E d \in Data : Send(d)

-----------------------------------------------------------------------------
(* Receiver actions *)

ReceiverBecomeReady ==
  /\ ~recvReady
  /\ recvReady' = TRUE
  /\ rcvStatus' = "waiting"
  /\ UNCHANGED <<chan, sendReady, ack, fresh, sentLog, recvLog>>

ReceiverWithdraw ==
  /\ recvReady
  /\ recvReady' = FALSE
  /\ rcvStatus' = "idle"
  /\ UNCHANGED <<chan, sendReady, ack, fresh, sentLog, recvLog>>

\* The receiver consumes the datum in the channel.
Receive ==
  /\ recvReady
  /\ chan # NoData
  /\ recvLog' = Append(recvLog, chan)
  /\ chan' = NoData
  /\ ack' = TRUE
  /\ fresh' = FALSE
  /\ rcvStatus' = "got"
  /\ UNCHANGED <<sendReady, recvReady, sentLog>>

\* The receiver observes that no datum is present.
Poll ==
  /\ recvReady
  /\ rcvStatus = "waiting"
  /\ chan = NoData
  /\ rcvStatus' = "empty"
  /\ UNCHANGED <<chan, sendReady, ack, recvReady, fresh, sentLog, recvLog>>

\* The receiver, still ready, starts a new attempt.
Retry ==
  /\ recvReady
  /\ rcvStatus \in {"got", "empty"}
  /\ rcvStatus' = "waiting"
  /\ UNCHANGED <<chan, sendReady, ack, recvReady, fresh, sentLog, recvLog>>

RecvAttempt == Receive \/ Poll

ReceiverStep == ReceiverBecomeReady \/ ReceiverWithdraw \/ Receive \/ Poll \/ Retry

-----------------------------------------------------------------------------
Next == SenderStep \/ ReceiverStep

Fairness ==
  /\ WF_vars(SenderStep)
  /\ WF_vars(Receive)
  /\ WF_vars(RecvAttempt)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* The channel holds at most one datum: either empty, or exactly the one
\* outstanding datum, and at most one datum is in flight.
AtMostOneDatum ==
  /\ chan \in Data \cup {NoData}
  /\ Len(sentLog) - Len(recvLog) \in {0, 1}
  /\ (chan # NoData) <=> (Len(sentLog) = Len(recvLog) + 1)
  /\ (chan # NoData) => chan = sentLog[Len(sentLog)]

\* Receiver never consumes a datum that was never sent (in order).
NoPhantomReceive ==
  /\ Len(recvLog) <= Len(sentLog)
  /\ \A i \in 1..Len(recvLog) : recvLog[i] = sentLog[i]

\* Acknowledgment holds exactly when every sent datum has been delivered.
AckCorrect ==
  /\ ack <=> (Len(recvLog) = Len(sentLog))
  /\ ack => chan = NoData

\* Handshake signals are consistent with the channel state.
SignalsConsistent ==
  /\ fresh <=> (chan # NoData)
  /\ sendReady => ack
  /\ (rcvStatus = "idle") <=> ~recvReady

Safety == TypeOK /\ AtMostOneDatum /\ NoPhantomReceive /\ AckCorrect /\ SignalsConsistent

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties *)

\* A datum offered while the receiver remains ready is eventually consumed.
DeliveryLiveness ==
  (chan # NoData /\ recvReady) ~> (chan = NoData \/ ~recvReady)

\* Every offered datum is eventually consumed if the receiver stays ready forever.
EventualConsumption ==
  \A n \in 1..MaxMsgs :
    ([]recvReady /\ <>(Len(sentLog) >= n)) => <>(Len(recvLog) >= n)

\* A receiver continuously attempting eventually obtains a datum or sees none.
ReceiveProgress ==
  (rcvStatus = "waiting") ~> (rcvStatus \in {"got", "empty"} \/ ~recvReady)

THEOREM Spec => DeliveryLiveness /\ EventualConsumption /\ ReceiveProgress
=============================================================================