---------------------------- MODULE HandshakeFIFO ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Message,   \* abstract set of messages
          N          \* capacity of the internal queue

ASSUME N \in Nat \ {0}
ASSUME Message # {}

VARIABLES in,        \* input channel  [val, rdy, ack]
          out,       \* output channel [val, rdy, ack]
          q,         \* internal FIFO queue
          sent,      \* history: messages sent by the producer, in order
          delivered  \* history: messages taken by the consumer, in order

vars == <<in, out, q, sent, delivered>>

-----------------------------------------------------------------------------
(* Channel abstraction: a single-slot handshake channel                     *)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanPending(c) == c.rdy # c.ack          \* a value is waiting in the slot
ChanFree(c)    == c.rdy = c.ack          \* slot may accept a new value

\* Contents of a channel as a sequence (0 or 1 element)
ChanContents(c) == IF ChanPending(c) THEN <<c.val>> ELSE <<>>

IsPrefix(s, t) == /\ Len(s) =< Len(t)
                  /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
Init == /\ \E m \in Message : in  = [val |-> m, rdy |-> 0, ack |-> 0]
        /\ \E m \in Message : out = [val |-> m, rdy |-> 0, ack |-> 0]
        /\ q = << >>
        /\ sent = << >>
        /\ delivered = << >>

-----------------------------------------------------------------------------
(* Producer sends msg on the input channel (raises rdy)                     *)
SSend(msg) == /\ ChanFree(in)
              /\ in' = [in EXCEPT !.val = msg, !.rdy = 1 - @]
              /\ sent' = Append(sent, msg)
              /\ UNCHANGED <<out, q, delivered>>

(* Buffer receives from input channel and enqueues (raises ack)             *)
BufRcv == /\ ChanPending(in)
          /\ Len(q) < N
          /\ q' = Append(q, in.val)
          /\ in' = [in EXCEPT !.ack = 1 - @]
          /\ UNCHANGED <<out, sent, delivered>>

(* Buffer dequeues and sends head on the output channel (raises rdy)        *)
BufSend == /\ q # << >>
           /\ ChanFree(out)
           /\ out' = [out EXCEPT !.val = Head(q), !.rdy = 1 - @]
           /\ q' = Tail(q)
           /\ UNCHANGED <<in, sent, delivered>>

(* Consumer receives from the output channel (raises ack)                   *)
RRcv == /\ ChanPending(out)
        /\ out' = [out EXCEPT !.ack = 1 - @]
        /\ delivered' = Append(delivered, out.val)
        /\ UNCHANGED <<in, q, sent>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(BufRcv) /\ WF_vars(BufSend) /\ WF_vars(RRcv)

-----------------------------------------------------------------------------
(* Safety invariants                                                        *)
TypeOK == /\ in  \in ChanType
          /\ out \in ChanType
          /\ q \in Seq(Message)
          /\ Len(q) =< N
          /\ sent \in Seq(Message)
          /\ delivered \in Seq(Message)

\* Queue is always a finite sequence of messages within capacity
QueueBounded == /\ q \in Seq(Message)
                /\ Len(q) \in 0..N

\* Handshake consistency: rdy/ack are bits and at most one value in flight
HandshakeOK == /\ in.rdy  \in {0, 1} /\ in.ack  \in {0, 1}
               /\ out.rdy \in {0, 1} /\ out.ack \in {0, 1}
               /\ Len(ChanContents(in))  =< 1
               /\ Len(ChanContents(out)) =< 1

\* No loss, no creation, FIFO order: everything sent is exactly what has been
\* delivered, followed by what is in transit, in sending order.
Conservation ==
    sent = delivered \o ChanContents(out) \o q \o ChanContents(in)

\* Every delivered message was previously sent, in the same order
FIFOOrder == IsPrefix(delivered, sent)

\* Every message in the buffer or on the output channel was sent
NoCreation ==
    /\ \A i \in 1..Len(q) : \E j \in 1..Len(sent) : sent[j] = q[i]
    /\ ChanPending(out) => \E j \in 1..Len(sent) : sent[j] = out.val

InFlightBounded == Len(sent) - Len(delivered) =< N + 2

Inv == /\ TypeOK
       /\ QueueBounded
       /\ HandshakeOK
       /\ Conservation
       /\ FIFOOrder
       /\ NoCreation
       /\ InFlightBounded

-----------------------------------------------------------------------------
(* Action-level safety properties: no unauthorized updates                  *)

\* ready and ack alternate correctly on each channel
InRdyAlternates  == [][in.rdy'  # in.rdy  => ChanFree(in)]_vars
InAckAlternates  == [][in.ack'  # in.ack  => ChanPending(in)]_vars
OutRdyAlternates == [][out.rdy' # out.rdy => ChanFree(out)]_vars
OutAckAlternates == [][out.ack' # out.ack => ChanPending(out)]_vars

\* Channel values change only together with a send handshake
InValGuarded  == [][in.val'  # in.val  => in.rdy'  # in.rdy]_vars
OutValGuarded == [][out.val' # out.val => out.rdy' # out.rdy]_vars

\* Histories only grow by appending
HistoryMonotone == [][ /\ IsPrefix(sent, sent')
                       /\ IsPrefix(delivered, delivered') ]_vars

\* The queue only changes via enqueue (BufRcv) or dequeue (BufSend)
QueueGuarded == [][q' # q => (BufRcv \/ BufSend)]_vars

ActionSafety == /\ InRdyAlternates /\ InAckAlternates
                /\ OutRdyAlternates /\ OutAckAlternates
                /\ InValGuarded /\ OutValGuarded
                /\ HistoryMonotone /\ QueueGuarded

-----------------------------------------------------------------------------
(* Liveness (under FairSpec): every sent message is eventually delivered    *)
EventualDelivery ==
    \A k \in Nat : (Len(sent) >= k) ~> (Len(delivered) >= k)

THEOREM Spec => []Inv
THEOREM Spec => ActionSafety
THEOREM FairSpec => EventualDelivery
=============================================================================