------------------------------ MODULE ReliableMulticast ------------------------------
(***************************************************************************)
(* Reliable, in-order delivery of numbered tuples from one sender to a     *)
(* set of receivers over lossy, duplicating, reordering (but              *)
(* non-corrupting) channels.                                               *)
(*                                                                         *)
(* Protocol: sliding-window selective-repeat with cumulative acks.         *)
(*  - The sender keeps at most W unacknowledged tuples (window).           *)
(*  - Each receiver buffers at most W out-of-order tuples (rbuf) and       *)
(*    delivers strictly in sequence order.                                 *)
(*  - The sender garbage-collects a tuple once every receiver has          *)
(*    cumulatively acknowledged it; receivers discard buffered entries as  *)
(*    soon as they are delivered.                                          *)
(* MaxSeq bounds the run only to make model checking finite; the protocol  *)
(* state (window, rbuf) is bounded by W independently of MaxSeq.           *)
(* sentLog and delivered are history (ghost) variables used only to state  *)
(* correctness properties.                                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Tuples,      \* finite set of tuple values
          Receivers,   \* set of receivers
          W,           \* window size (memory bound)
          MaxSeq       \* bound on number of tuples sent (for model checking)

ASSUME /\ Tuples # {}
       /\ Receivers # {}
       /\ W \in Nat \ {0}
       /\ MaxSeq \in Nat

VARIABLES
  nextSeq,    \* sequence number to assign to the next new tuple
  base,       \* lowest sequence number still held by the sender
  window,     \* sender buffer: window[i] is tuple with seq base+i-1
  acked,      \* acked[r]: highest cumulative ack the sender received from r
  expected,   \* expected[r]: next sequence number receiver r will deliver
  rbuf,       \* rbuf[r]: out-of-order messages buffered at receiver r
  dataChan,   \* dataChan[r]: set of data messages in transit to r
  ackChan,    \* ackChan[r]: set of cumulative acks in transit from r
  sentLog,    \* ghost: sequence of all tuples sent, in order
  delivered   \* ghost: delivered[r] = sequence of delivered [seq, val]

vars == <<nextSeq, base, window, acked, expected, rbuf,
          dataChan, ackChan, sentLog, delivered>>

Msgs == [seq : 1..MaxSeq, val : Tuples]

Max(a, b) == IF a >= b THEN a ELSE b

-----------------------------------------------------------------------------
TypeOK ==
  /\ nextSeq \in 1..(MaxSeq + 1)
  /\ base \in 1..(MaxSeq + 1)
  /\ window \in Seq(Tuples)
  /\ acked \in [Receivers -> 0..MaxSeq]
  /\ expected \in [Receivers -> 1..(MaxSeq + 1)]
  /\ rbuf \in [Receivers -> SUBSET Msgs]
  /\ dataChan \in [Receivers -> SUBSET Msgs]
  /\ ackChan \in [Receivers -> SUBSET (0..MaxSeq)]
  /\ sentLog \in Seq(Tuples)
  /\ delivered \in [Receivers -> Seq(Msgs)]

Init ==
  /\ nextSeq = 1
  /\ base = 1
  /\ window = << >>
  /\ acked = [r \in Receivers |-> 0]
  /\ expected = [r \in Receivers |-> 1]
  /\ rbuf = [r \in Receivers |-> {}]
  /\ dataChan = [r \in Receivers |-> {}]
  /\ ackChan = [r \in Receivers |-> {}]
  /\ sentLog = << >>
  /\ delivered = [r \in Receivers |-> << >>]

-----------------------------------------------------------------------------
(* Sender: transmit a new tuple to all receivers, if the window has room. *)
Send(t) ==
  /\ nextSeq <= MaxSeq
  /\ Len(window) < W
  /\ window' = Append(window, t)
  /\ sentLog' = Append(sentLog, t)
  /\ nextSeq' = nextSeq + 1
  /\ dataChan' = [r \in Receivers |->
                    dataChan[r] \cup {[seq |-> nextSeq, val |-> t]}]
  /\ UNCHANGED <<base, acked, expected, rbuf, ackChan, delivered>>

(* Sender: retransmit a tuple not yet acknowledged by receiver r. *)
Retransmit(r, s) ==
  /\ s \in (acked[r] + 1)..(nextSeq - 1)
  /\ LET m == [seq |-> s, val |-> window[s - base + 1]]
     IN  /\ m \notin dataChan[r]
         /\ dataChan' = [dataChan EXCEPT ![r] = @ \cup {m}]
  /\ UNCHANGED <<nextSeq, base, window, acked, expected, rbuf,
                 ackChan, sentLog, delivered>>

RetransmitNext(r) == Retransmit(r, acked[r] + 1)

(* Sender: receive a cumulative ack from r (copy may remain: duplication). *)
RcvAck(r, a, keep) ==
  /\ a \in ackChan[r]
  /\ acked' = [acked EXCEPT ![r] = Max(@, a)]
  /\ ackChan' = IF keep THEN ackChan
                ELSE [ackChan EXCEPT ![r] = @ \ {a}]
  /\ UNCHANGED <<nextSeq, base, window, expected, rbuf,
                 dataChan, sentLog, delivered>>

RcvNewAck(r) ==
  \E a \in ackChan[r], keep \in BOOLEAN : a > acked[r] /\ RcvAck(r, a, keep)

(* Sender garbage collection: drop the oldest tuple once all receivers  *)
(* have cumulatively acknowledged it.                                   *)
SenderGC ==
  /\ Len(window) > 0
  /\ \A r \in Receivers : acked[r] >= base
  /\ window' = Tail(window)
  /\ base' = base + 1
  /\ UNCHANGED <<nextSeq, acked, expected, rbuf, dataChan, ackChan,
                 sentLog, delivered>>

-----------------------------------------------------------------------------
(* Receiver: receive a data message (copy may remain: duplication).     *)
(* In-window messages are buffered; stale duplicates trigger a re-ack.  *)
RcvData(r, m, keep) ==
  /\ m \in dataChan[r]
  /\ dataChan' = IF keep THEN dataChan
                 ELSE [dataChan EXCEPT ![r] = @ \ {m}]
  /\ IF m.seq >= expected[r] /\ m.seq < expected[r] + W
       THEN /\ rbuf' = [rbuf EXCEPT ![r] = @ \cup {m}]
            /\ UNCHANGED ackChan
       ELSE /\ ackChan' = [ackChan EXCEPT ![r] = @ \cup {expected[r] - 1}]
            /\ UNCHANGED rbuf
  /\ UNCHANGED <<nextSeq, base, window, acked, expected, sentLog, delivered>>

RcvTarget(r) ==
  \E m \in dataChan[r], keep \in BOOLEAN :
     m.seq = acked[r] + 1 /\ RcvData(r, m, keep)

(* Receiver: deliver next in-order tuple, free its buffer slot, ack. *)
Deliver(r) ==
  \E m \in rbuf[r] :
    /\ m.seq = expected[r]
    /\ delivered' = [delivered EXCEPT ![r] = Append(@, m)]
    /\ expected' = [expected EXCEPT ![r] = @ + 1]
    /\ rbuf' = [rbuf EXCEPT ![r] = @ \ {m}]
    /\ ackChan' = [ackChan EXCEPT ![r] = @ \cup {expected[r]}]
    /\ UNCHANGED <<nextSeq, base, window, acked, dataChan, sentLog>>

-----------------------------------------------------------------------------
(* Unreliable network: loss of data and ack messages. Reordering is     *)
(* inherent in the set-based channels; duplication via keep = TRUE.     *)
LoseData(r, m) ==
  /\ m \in dataChan[r]
  /\ dataChan' = [dataChan EXCEPT ![r] = @ \ {m}]
  /\ UNCHANGED <<nextSeq, base, window, acked, expected, rbuf,
                 ackChan, sentLog, delivered>>

LoseAck(r, a) ==
  /\ a \in ackChan[r]
  /\ ackChan' = [ackChan EXCEPT ![r] = @ \ {a}]
  /\ UNCHANGED <<nextSeq, base, window, acked, expected, rbuf,
                 dataChan, sentLog, delivered>>

-----------------------------------------------------------------------------
Next ==
  \/ \E t \in Tuples : Send(t)
  \/ \E r \in Receivers, s \in 1..MaxSeq : Retransmit(r, s)
  \/ \E r \in Receivers, a \in 0..MaxSeq, keep \in BOOLEAN : RcvAck(r, a, keep)
  \/ SenderGC
  \/ \E r \in Receivers, m \in Msgs, keep \in BOOLEAN : RcvData(r, m, keep)
  \/ \E r \in Receivers : Deliver(r)
  \/ \E r \in Receivers, m \in Msgs : LoseData(r, m)
  \/ \E r \in Receivers, a \in 0..MaxSeq : LoseAck(r, a)

(* Fairness: the sender keeps retransmitting the oldest unacked tuple,  *)
(* receivers deliver and the sender GCs when able; a message that is    *)
(* retransmitted infinitely often is eventually received (strong        *)
(* fairness), for both data and acks.                                   *)
Fairness ==
  /\ \A r \in Receivers :
       /\ WF_vars(RetransmitNext(r))
       /\ WF_vars(Deliver(r))
       /\ SF_vars(RcvTarget(r))
       /\ SF_vars(RcvNewAck(r))
  /\ WF_vars(SenderGC)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

NoSpuriousDelivery ==
  \A r \in Receivers : \A i \in 1..Len(delivered[r]) :
     LET m == delivered[r][i]
     IN  /\ m.seq \in 1..Len(sentLog)
         /\ sentLog[m.seq] = m.val

NoDuplicateDelivery ==
  \A r \in Receivers : \A i, j \in 1..Len(delivered[r]) :
     i # j => delivered[r][i].seq # delivered[r][j].seq

InOrderDelivery ==
  \A r \in Receivers :
     /\ Len(delivered[r]) <= Len(sentLog)
     /\ \A i \in 1..Len(delivered[r]) :
          /\ delivered[r][i].seq = i
          /\ delivered[r][i].val = sentLog[i]

BoundedMemory ==
  /\ Len(window) <= W
  /\ \A r \in Receivers : Cardinality(rbuf[r]) <= W

WindowConsistent ==
  /\ nextSeq = base + Len(window)
  /\ \A r \in Receivers : base <= acked[r] + 1 /\ acked[r] < expected[r]

Safety ==
  /\ TypeOK
  /\ NoSpuriousDelivery
  /\ NoDuplicateDelivery
  /\ InOrderDelivery
  /\ BoundedMemory
  /\ WindowConsistent

-----------------------------------------------------------------------------
(* Liveness properties *)

EventualDelivery ==
  \A r \in Receivers, i \in 1..MaxSeq :
     (Len(sentLog) >= i) ~> (Len(delivered[r]) >= i)

EventualReclamation ==
  \A i \in 1..MaxSeq : (Len(sentLog) >= i) ~> (base > i)

Liveness == EventualDelivery /\ EventualReclamation

THEOREM Spec => []Safety
THEOREM Spec => Liveness
==============================================================================