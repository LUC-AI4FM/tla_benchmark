---------------------------- MODULE MCInnerFIFO ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message, qLen

VARIABLES in, out, q

-----------------------------------------------------------------------------
(* Channel operations, as in the InnerFIFOInstanced specification          *)

ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in ChanType
               /\ c.ack = c.rdy

ChanSend(c, d) == /\ c.rdy = c.ack
                  /\ c' = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c) == /\ c.rdy # c.ack
              /\ c' = [c EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------
(* InnerFIFO specification                                                 *)

Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

TypeInvariant == /\ in \in ChanType
                 /\ out \in ChanType
                 /\ q \in Seq(Message)

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

Spec == Init /\ [][Next]_<<in, out, q>>

-----------------------------------------------------------------------------
(* Model-checking constraint                                               *)

qConstraint == Len(q) \leq qLen

=============================================================================