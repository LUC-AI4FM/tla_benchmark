----------------------------- MODULE AsyncSingleBitHandshake -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT DATA
ASSUME DATA /= {}

VARIABLES
  r,        \* sender's ready bit
  a,        \* receiver's acknowledge bit
  data,     \* data value currently published on the channel
  sendBuf,  \* sender's local next-to-publish buffer (not visible to receiver)
  sent,     \* sequence (history) of committed values (on ready toggle)
  recv      \* sequence (history) of delivered values (on acknowledge toggle)

vars == << r, a, data, sendBuf, sent, recv >>

Init ==
  /\ r \in BOOLEAN
  /\ a = r
  /\ data \in DATA
  /\ sendBuf \in DATA
  /\ sent = << >>
  /\ recv = << >>

IsPrefix(s, t) ==
  /\ Len(s) <= Len(t)
  /\ s = SubSeq(t, 1, Len(s))

SenderPrepare ==
  /\ sendBuf' \in DATA
  /\ UNCHANGED << r, a, data, sent, recv >>

SenderCommit ==
  /\ r = a
  /\ r' = ~r
  /\ data' = sendBuf
  /\ sent' = Append(sent, sendBuf)
  /\ UNCHANGED << a, sendBuf, recv >>

ReceiverAck ==
  /\ r # a
  /\ a' = ~a
  /\ recv' = Append(recv, data)
  /\ UNCHANGED << r, data, sendBuf, sent >>

Next ==
  \/ SenderPrepare
  \/ SenderCommit
  \/ ReceiverAck

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(ReceiverAck)

TypeSafety ==
  /\ r \in BOOLEAN
  /\ a \in BOOLEAN
  /\ data \in DATA
  /\ sendBuf \in DATA
  /\ sent \in Seq(DATA)
  /\ recv \in Seq(DATA)

DataIntegrity ==
  /\ IsPrefix(recv, sent)

BitsAlternationInv ==
  /\ (Len(sent) = Len(recv)) <=> (r = a)
  /\ (Len(sent) = Len(recv) + 1) <=> (r # a)

SafetyInvariant ==
  /\ TypeSafety
  /\ DataIntegrity
  /\ BitsAlternationInv

EventualAckPerSend ==
  [] ( (Len(sent) > Len(recv)) => <> (Len(sent) = Len(recv)) )

Pending == (r # a)
EventualAckByBits ==
  [] ( Pending => <> ~Pending )

==========================================================================================