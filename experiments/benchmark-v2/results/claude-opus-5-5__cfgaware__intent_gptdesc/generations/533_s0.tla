---------------------------- MODULE ReliableMulticast ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ConstMinValue == 0
ConstTuples   == {<<1, "a">>, <<2, "b">>}

ASSUME minValue \in Nat
ASSUME Tuples # {} /\ IsFiniteSet(Tuples)

Receivers == {"r1", "r2"}
MaxSeq    == 3
Window    == 2

SeqRange  == minValue .. (minValue + MaxSeq - 1)
AckRange  == minValue .. (minValue + MaxSeq)

DataMsgs  == [rcv : Receivers, seq : SeqRange, val : Tuples]
AckMsgs   == [rcv : Receivers, ack : AckRange]

VARIABLES
    nextSeq,
    sendBuf,
    sent,
    acked,
    msgs,
    acks,
    expected,
    rbuf,
    delivered

vars == <<nextSeq, sendBuf, sent, acked, msgs, acks, expected, rbuf, delivered>>

Min(S) == CHOOSE v \in S : \A w \in S : v <= w
LowAck == Min({acked[r] : r \in Receivers})

TypeOK ==
    /\ nextSeq \in minValue .. (minValue + MaxSeq)
    /\ DOMAIN sendBuf \subseteq SeqRange
    /\ \A s \in DOMAIN sendBuf : sendBuf[s] \in Tuples
    /\ sent \in Seq(Tuples)
    /\ acked \in [Receivers -> AckRange]
    /\ msgs \subseteq DataMsgs
    /\ acks \subseteq AckMsgs
    /\ expected \in [Receivers -> AckRange]
    /\ \A r \in Receivers : rbuf[r] \subseteq [seq : SeqRange, val : Tuples]
    /\ \A r \in Receivers : delivered[r] \in Seq([seq : SeqRange, val : Tuples])

Init ==
    /\ nextSeq = minValue
    /\ sendBuf = [s \in {} |-> CHOOSE t \in Tuples : TRUE]
    /\ sent = <<>>
    /\ acked = [r \in Receivers |-> minValue]
    /\ msgs = {}
    /\ acks = {}
    /\ expected = [r \in Receivers |-> minValue]
    /\ rbuf = [r \in Receivers |-> {}]
    /\ delivered = [r \in Receivers |-> <<>>]

SendNew(t) ==
    /\ nextSeq < minValue + MaxSeq
    /\ nextSeq < LowAck + Window
    /\ Cardinality(DOMAIN sendBuf) < Window
    /\ sendBuf' = sendBuf @@ (nextSeq :> t)
    /\ sent' = Append(sent, t)
    /\ msgs' = msgs \cup {[rcv |-> r, seq |-> nextSeq, val |-> t] : r \in Receivers}
    /\ nextSeq' = nextSeq + 1
    /\ UNCHANGED <<acked, acks, expected, rbuf, delivered>>

Retransmit(r, s) ==
    /\ s \in DOMAIN sendBuf
    /\ s >= acked[r]
    /\ [rcv |-> r, seq |-> s, val |-> sendBuf[s]] \notin msgs
    /\ msgs' = msgs \cup {[rcv |-> r, seq |-> s, val |-> sendBuf[s]]}
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, acks, expected, rbuf, delivered>>

LoseData(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, acks, expected, rbuf, delivered>>

Receive(m) ==
    /\ m \in msgs
    /\ m.seq >= expected[m.rcv]
    /\ m.seq < expected[m.rcv] + Window
    /\ [seq |-> m.seq, val |-> m.val] \notin rbuf[m.rcv]
    /\ rbuf' = [rbuf EXCEPT ![m.rcv] = @ \cup {[seq |-> m.seq, val |-> m.val]}]
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, msgs, acks, expected, delivered>>

Deliver(r) ==
    /\ \E e \in rbuf[r] :
        /\ e.seq = expected[r]
        /\ delivered' = [delivered EXCEPT ![r] = Append(@, e)]
        /\ expected' = [expected EXCEPT ![r] = @ + 1]
        /\ rbuf' = [rbuf EXCEPT ![r] = {x \in @ : x.seq > e.seq}]
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, msgs, acks>>

SendAck(r) ==
    /\ [rcv |-> r, ack |-> expected[r]] \notin acks
    /\ acks' = acks \cup {[rcv |-> r, ack |-> expected[r]]}
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, msgs, expected, rbuf, delivered>>

LoseAck(a) ==
    /\ a \in acks
    /\ acks' = acks \ {a}
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, msgs, expected, rbuf, delivered>>

RecvAck(a) ==
    /\ a \in acks
    /\ a.ack > acked[a.rcv]
    /\ acked' = [acked EXCEPT ![a.rcv] = a.ack]
    /\ UNCHANGED <<nextSeq, sendBuf, sent, msgs, acks, expected, rbuf, delivered>>

SenderGC ==
    /\ \E s \in DOMAIN sendBuf : s < LowAck
    /\ sendBuf' = [s \in {x \in DOMAIN sendBuf : x >= LowAck} |-> sendBuf[s]]
    /\ UNCHANGED <<nextSeq, sent, acked, msgs, acks, expected, rbuf, delivered>>

ChannelGC(m) ==
    /\ m \in msgs
    /\ m.seq < expected[m.rcv]
    /\ m.seq < acked[m.rcv]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<nextSeq, sendBuf, sent, acked, acks, expected, rbuf, delivered>>

Done ==
    /\ nextSeq = minValue + MaxSeq
    /\ \A r \in Receivers : acked[r] = nextSeq
    /\ DOMAIN sendBuf = {}
    /\ UNCHANGED vars

Next ==
    \/ \E t \in Tuples : SendNew(t)
    \/ \E r \in Receivers, s \in SeqRange : Retransmit(r, s)
    \/ \E m \in msgs : LoseData(m) \/ Receive(m) \/ ChannelGC(m)
    \/ \E r \in Receivers : Deliver(r) \/ SendAck(r)
    \/ \E a \in acks : LoseAck(a) \/ RecvAck(a)
    \/ SenderGC
    \/ Done

Fairness ==
    /\ \A r \in Receivers, s \in SeqRange : WF_vars(Retransmit(r, s))
    /\ \A m \in DataMsgs : SF_vars(Receive(m))
    /\ \A r \in Receivers : WF_vars(Deliver(r))
    /\ \A r \in Receivers : WF_vars(SendAck(r))
    /\ \A a \in AckMsgs : SF_vars(RecvAck(a))
    /\ WF_vars(SenderGC)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety properties
NoSpuriousDelivery ==
    \A r \in Receivers : \A i \in 1 .. Len(delivered[r]) :
        /\ i <= Len(sent)
        /\ delivered[r][i].val = sent[delivered[r][i].seq - minValue + 1]

NoDuplicates ==
    \A r \in Receivers : \A i, j \in 1 .. Len(delivered[r]) :
        i # j => delivered[r][i].seq # delivered[r][j].seq

InOrder ==
    \A r \in Receivers : \A i \in 1 .. Len(delivered[r]) :
        delivered[r][i].seq = minValue + i - 1

BoundedMemory ==
    /\ Cardinality(DOMAIN sendBuf) <= Window
    /\ \A r \in Receivers : Cardinality(rbuf[r]) <= Window

Safety == NoSpuriousDelivery /\ NoDuplicates /\ InOrder /\ BoundedMemory

\* Liveness properties
EventualDelivery ==
    \A s \in SeqRange : \A r \in Receivers :
        (nextSeq > s) ~> (Len(delivered[r]) > s - minValue)

EventualReclaim ==
    \A s \in SeqRange :
        (nextSeq > s) ~> (s \notin DOMAIN sendBuf /\ LowAck > s)

Liveness == EventualDelivery /\ EventualReclaim

==================================================================================