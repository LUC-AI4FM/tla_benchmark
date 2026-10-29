------------------------------ MODULE BufferedFIFO ------------------------------
(***************************************************************************)
(* A buffered FIFO queue that connects an external sender to an external   *)
(* receiver through two asynchronous two-phase handshake channels:         *)
(*                                                                         *)
(*     Sender --[in]--> Buffer q --[out]--> Receiver                       *)
(*                                                                         *)
(* Each channel is a record with a data value and two one-bit signals,     *)
(* rdy and ack:                                                            *)
(*   - Send is enabled when rdy = ack. It writes val and toggles rdy.      *)
(*   - Receive is enabled when rdy # ack. It toggles ack.                  *)
(*                                                                         *)
(* The history variables sentLog and recvLog record every message the      *)
(* external sender transmits and every message the external receiver       *)
(* accepts. They exist only to state the FIFO ordering property and do     *)
(* not affect the behavior of the system.                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message            \* The set of messages that can be transmitted

VARIABLES
    in,                     \* Input channel  (sender -> buffer)
    out,                    \* Output channel (buffer -> receiver)
    q,                      \* Internal FIFO buffer
    sentLog,                \* History: messages sent by the sender
    recvLog                 \* History: messages accepted by the receiver

vars == <<in, out, q, sentLog, recvLog>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Generic handshake channel definitions                                   *)
(***************************************************************************)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == c \in ChanType /\ c.rdy = c.ack

\* The send operation on channel c, with the new channel value c2.
ChanSend(c, c2, d) ==
    /\ c.rdy = c.ack
    /\ c2 = [c EXCEPT !.val = d, !.rdy = 1 - @]

\* The receive operation on channel c, with the new channel value c2.
ChanRcv(c, c2) ==
    /\ c.rdy # c.ack
    /\ c2 = [c EXCEPT !.ack = 1 - @]

\* The message pending on a channel: one message if a send has not yet been
\* acknowledged, otherwise none.
Pending(c) == IF c.rdy # c.ack THEN <<c.val>> ELSE <<>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ ChanInit(in)
    /\ ChanInit(out)
    /\ q = << >>
    /\ sentLog = << >>
    /\ recvLog = << >>

(***************************************************************************)
(* Operations                                                              *)
(***************************************************************************)

\* 1. The external sender places message msg on the input channel.
SSend(msg) ==
    /\ ChanSend(in, in', msg)
    /\ sentLog' = Append(sentLog, msg)
    /\ UNCHANGED <<out, q, recvLog>>

\* 2. The buffer accepts a message from the input channel and enqueues it.
BufRcv ==
    /\ ChanRcv(in, in')
    /\ q' = Append(q, in.val)
    /\ UNCHANGED <<out, sentLog, recvLog>>

\* 3. The buffer dequeues a message and places it on the output channel.
\*    It is enabled only when the buffer is non-empty.
BufSend ==
    /\ q # << >>
    /\ ChanSend(out, out', Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED <<in, sentLog, recvLog>>

\* 4. The external receiver completes reception from the output channel.
RRcv ==
    /\ ChanRcv(out, out')
    /\ recvLog' = Append(recvLog, out.val)
    /\ UNCHANGED <<in, q, sentLog>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* 1. Type safety: both channels are well formed, with data drawn from
\*    Message and binary signals. The buffer is a sequence of messages.
TypeOK ==
    /\ in \in ChanType
    /\ out \in ChanType
    /\ q \in Seq(Message)
    /\ sentLog \in Seq(Message)
    /\ recvLog \in Seq(Message)

\* 2. FIFO ordering, stated as a state invariant. The sequence of all
\*    messages sent equals the messages already received, then the message
\*    pending on the output channel, then the buffer contents in order, then
\*    the message pending on the input channel. Nothing is lost, duplicated
\*    or reordered.
FIFOInvariant ==
    sentLog = recvLog \o Pending(out) \o q \o Pending(in)

\* A direct consequence: the receiver always sees a prefix of what was sent.
RecvIsPrefixOfSent ==
    /\ Len(recvLog) <= Len(sentLog)
    /\ recvLog = SubSeq(sentLog, 1, Len(recvLog))

\* 2'. FIFO ordering as an action property on the buffer. The buffer only
\*     appends at the tail or removes from the head, and a dequeued element
\*     is exactly the one placed on the output channel.
BufferIsQueue ==
    [][ \/ q' = q
        \/ q' = Append(q, in.val)
        \/ (q # << >> /\ q' = Tail(q) /\ out'.val = Head(q)) ]_q

\* 3. Handshake protocol integrity.
\*    (a) rdy toggles only when rdy = ack held before the step (a send).
\*    (b) ack toggles only when rdy # ack held before the step (a receive).
\*    (c) rdy and ack never change in the same step.
HandshakeStep(c, c2) ==
    /\ (c2.rdy # c.rdy) => (c.rdy = c.ack /\ c2.rdy = 1 - c.rdy)
    /\ (c2.ack # c.ack) => (c.rdy # c.ack /\ c2.ack = 1 - c.ack)
    /\ ~(c2.rdy # c.rdy /\ c2.ack # c.ack)
    /\ (c2.val # c.val) => (c2.rdy # c.rdy)

HandshakeIntegrity ==
    /\ [][HandshakeStep(in, in')]_in
    /\ [][HandshakeStep(out, out')]_out

\* At any moment each channel has at most one message in transit.
AtMostOnePending ==
    /\ Len(Pending(in)) <= 1
    /\ Len(Pending(out)) <= 1

Safety == TypeOK /\ FIFOInvariant /\ RecvIsPrefixOfSent /\ AtMostOnePending

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => BufferIsQueue
THEOREM Spec => HandshakeIntegrity
=============================================================================