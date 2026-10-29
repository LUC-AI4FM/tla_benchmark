------------------------------ MODULE InnerFIFO ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

Capacity == 1

Channel == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in Channel
               /\ c.ack = c.rdy

ChanSend(c, cp, d) == /\ c.rdy = c.ack
                      /\ cp = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c, cp) == /\ c.rdy # c.ack
                  /\ cp = [c EXCEPT !.ack = 1 - @]

Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

SSend(msg) == /\ ChanSend(in, in', msg)
              /\ UNCHANGED <<out, q>>

BufRcv == /\ Len(q) < Capacity
          /\ ChanRcv(in, in')
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

BufSend == /\ q # << >>
           /\ ChanSend(out, out', Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ ChanRcv(out, out')
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

TypeInvariant == /\ in \in Channel
                 /\ out \in Channel
                 /\ q \in Seq(Message)
                 /\ Len(q) <= Capacity

HandshakeConsistent == /\ in.rdy \in {0, 1} /\ in.ack \in {0, 1}
                       /\ out.rdy \in {0, 1} /\ out.ack \in {0, 1}

NoCreation == \A i \in 1..Len(q) : q[i] \in Message

Safety == TypeInvariant /\ HandshakeConsistent /\ NoCreation

THEOREM Spec => []TypeInvariant
=============================================================================