---------------------------- MODULE InnerFIFO ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

-----------------------------------------------------------------------------
(* Bound on the internal queue length, so the buffer is finite *)
QBound == 3

Channel == [val : Message, rdy : {0, 1}, ack : {0, 1}]

(* Two-phase handshake channel operators *)
ChanSend(v, chan) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = v, !.rdy = 1 - @]

ChanRcv(chan) ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ in \in Channel
    /\ out \in Channel
    /\ q \in Seq(Message)

Init ==
    /\ in \in {c \in Channel : c.ack = c.rdy}
    /\ out \in {c \in Channel : c.ack = c.rdy}
    /\ q = << >>

(* Sender puts a message on the input channel *)
SSend(msg) ==
    /\ ChanSend(msg, in)
    /\ UNCHANGED <<out, q>>

(* Buffer receives a message from the input channel and appends it to q *)
BufRcv ==
    /\ Len(q) < QBound
    /\ ChanRcv(in)
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

(* Buffer sends the head of q on the output channel *)
BufSend ==
    /\ q # << >>
    /\ ChanSend(Head(q), out)
    /\ q' = Tail(q)
    /\ UNCHANGED in

(* Receiver completes reception on the output channel *)
RRcv ==
    /\ ChanRcv(out)
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_<<in, out, q>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================