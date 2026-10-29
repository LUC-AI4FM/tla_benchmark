---------------------------- MODULE InnerFIFO ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

-----------------------------------------------------------------------------
(* Handshake channel operators *)

ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in ChanType
               /\ c.ack = c.rdy

ChanSend(c, d) == /\ c.rdy = c.ack
                  /\ c' = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c) == /\ c.rdy # c.ack
              /\ c' = [c EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------

TypeInvariant == /\ in \in ChanType
                 /\ out \in ChanType
                 /\ q \in Seq(Message)

Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

SSend(msg) == /\ ChanSend(in, msg)
              /\ UNCHANGED <<out, q>>

BufRcv == /\ ChanRcv(in)
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

BufSend == /\ q # << >>
           /\ ChanSend(out, Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ ChanRcv(out)
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================