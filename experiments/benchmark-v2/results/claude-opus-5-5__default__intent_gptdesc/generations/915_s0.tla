--------------------------- MODULE OneSlotHandshakeChannel ---------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

NoData == CHOOSE v : v \notin Data

VARIABLES
    buf,
    rdy,
    ack,
    sent,
    rcvd

vars == <<buf, rdy, ack, sent, rcvd>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ buf  \in Data \cup {NoData}
    /\ rdy  \in BOOLEAN
    /\ ack  \in BOOLEAN
    /\ sent \in Seq(Data)
    /\ rcvd \in Seq(Data)

Init ==
    /\ buf  = NoData
    /\ rdy  = FALSE
    /\ ack  = FALSE
    /\ sent = << >>
    /\ rcvd = << >>

-----------------------------------------------------------------------------
Send(d) ==
    /\ buf = NoData
    /\ buf'  = d
    /\ sent' = Append(sent, d)
    /\ UNCHANGED <<rdy, ack, rcvd>>

Ready ==
    /\ ~rdy
    /\ rdy' = TRUE
    /\ UNCHANGED <<buf, ack, sent, rcvd>>

Accept ==
    /\ buf # NoData
    /\ rdy
    /\ ~ack
    /\ rcvd' = Append(rcvd, buf)
    /\ ack'  = TRUE
    /\ rdy'  = FALSE
    /\ UNCHANGED <<buf, sent>>

Remove ==
    /\ ack
    /\ buf' = NoData
    /\ ack' = FALSE
    /\ UNCHANGED <<rdy, sent, rcvd>>

SenderStep   == (\E d \in Data : Send(d)) \/ Remove
ReceiverStep == Ready \/ Accept

Next == SenderStep \/ ReceiverStep

Fairness ==
    /\ WF_vars(\E d \in Data : Send(d))
    /\ WF_vars(Ready)
    /\ WF_vars(Accept)
    /\ WF_vars(Remove)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ s = SubSeq(t, 1, Len(s))

CapacityRespected ==
    /\ Len(rcvd) <= Len(sent)
    /\ Len(sent) - Len(rcvd) <= 1
    /\ (buf = NoData) => (Len(rcvd) = Len(sent) /\ ~ack)

NoCorruptionNoInvention ==
    /\ IsPrefix(rcvd, sent)
    /\ (buf # NoData) => (Len(sent) > 0 /\ buf = sent[Len(sent)])

AtMostOnceDelivery ==
    /\ (buf # NoData /\ ~ack) => Len(rcvd) = Len(sent) - 1
    /\ (buf # NoData /\  ack) => Len(rcvd) = Len(sent)

AckOnlyForOffered ==
    ack => /\ buf # NoData
           /\ Len(rcvd) > 0
           /\ Len(rcvd) = Len(sent)
           /\ rcvd[Len(rcvd)] = buf

Inv ==
    /\ TypeOK
    /\ CapacityRespected
    /\ NoCorruptionNoInvention
    /\ AtMostOnceDelivery
    /\ AckOnlyForOffered

ValueUnchangedWhileBuffered ==
    [][ (buf # NoData) => (buf' = buf \/ (ack /\ buf' = NoData)) ]_vars

AckStepOnlyForOffered ==
    [][ (~ack /\ ack') => /\ buf # NoData
                          /\ buf' = buf
                          /\ Len(sent) > 0
                          /\ buf = sent[Len(sent)]
                          /\ rcvd' = Append(rcvd, buf) ]_vars

DeliveryStepAtMostOnce ==
    [][ (rcvd' # rcvd) => /\ buf # NoData
                          /\ ~ack
                          /\ rcvd' = Append(rcvd, buf) ]_vars

SentHistoryAppendOnly ==
    [][ (sent' # sent) => (buf = NoData /\ \E d \in Data : sent' = Append(sent, d)) ]_vars

-----------------------------------------------------------------------------
EagerReceiverDelivery ==
    ([]<>rdy) =>
        \A k \in Nat : (Len(sent) >= k) ~> (Len(rcvd) >= k)

OfferedEventuallyAcked ==
    (buf # NoData /\ ~ack) ~> ack

AckedEventuallyCleared ==
    (buf # NoData) ~> (buf = NoData)

SenderProgress ==
    []<>(ENABLED <<SenderStep>>_vars) => []<><<SenderStep>>_vars

ReceiverProgress ==
    []<>(ENABLED <<ReceiverStep>>_vars) => []<><<ReceiverStep>>_vars

Liveness ==
    /\ EagerReceiverDelivery
    /\ OfferedEventuallyAcked
    /\ AckedEventuallyCleared
    /\ SenderProgress
    /\ ReceiverProgress

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => ValueUnchangedWhileBuffered /\ AckStepOnlyForOffered
                /\ DeliveryStepAtMostOnce /\ SentHistoryAppendOnly
THEOREM Spec => Liveness
=============================================================================