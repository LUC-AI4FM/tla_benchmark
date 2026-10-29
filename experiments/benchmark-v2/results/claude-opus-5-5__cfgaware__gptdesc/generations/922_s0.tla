------------------------------ MODULE InnerFIFO ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

-----------------------------------------------------------------------------
(* Expansion of  InChan == INSTANCE Channel WITH Data <- Message, chan <- in *)

InChan_TypeInvariant ==
    in \in [val : Message, rdy : {0, 1}, ack : {0, 1}]

InChan_Init ==
    /\ InChan_TypeInvariant
    /\ in.ack = in.rdy

InChan_Send(d) ==
    /\ in.rdy = in.ack
    /\ in' = [in EXCEPT !.val = d, !.rdy = 1 - @]

InChan_Rcv ==
    /\ in.rdy # in.ack
    /\ in' = [in EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------
(* Expansion of  OutChan == INSTANCE Channel WITH Data <- Message, chan <- out *)

OutChan_TypeInvariant ==
    out \in [val : Message, rdy : {0, 1}, ack : {0, 1}]

OutChan_Init ==
    /\ OutChan_TypeInvariant
    /\ out.ack = out.rdy

OutChan_Send(d) ==
    /\ out.rdy = out.ack
    /\ out' = [out EXCEPT !.val = d, !.rdy = 1 - @]

OutChan_Rcv ==
    /\ out.rdy # out.ack
    /\ out' = [out EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------

Init ==
    /\ InChan_Init
    /\ OutChan_Init
    /\ q = << >>

TypeInvariant ==
    /\ InChan_TypeInvariant
    /\ OutChan_TypeInvariant
    /\ q \in Seq(Message)

SSend(msg) ==
    /\ InChan_Send(msg)
    /\ UNCHANGED <<out, q>>

BufRcv ==
    /\ InChan_Rcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

BufSend ==
    /\ q # << >>
    /\ OutChan_Send(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in

RRcv ==
    /\ OutChan_Rcv
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