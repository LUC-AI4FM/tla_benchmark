---------------------------- MODULE InnerFIFO_ -------------------------------
(***************************************************************************)
(* TLC-oriented version of InnerFIFO. The INSTANCE statements for the      *)
(* input and output channels are expanded by hand into prefixed operators  *)
(* InChan_XXX and OutChan_XXX.                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* InChan == INSTANCE Channel WITH Data <- Message, chan <- in             *)
(***************************************************************************)
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
(***************************************************************************)
(* OutChan == INSTANCE Channel WITH Data <- Message, chan <- out           *)
(***************************************************************************)
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

\* Sender sends msg on channel in.
SSend(msg) ==
    /\ InChan_Send(msg)
    /\ UNCHANGED <<out, q>>

\* Buffer receives a message from channel in and appends it to q.
BufRcv ==
    /\ InChan_Rcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

\* Buffer sends Head(q) on channel out and removes it from q.
BufSend ==
    /\ q # << >>
    /\ OutChan_Send(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in

\* Receiver receives a message from channel out.
RRcv ==
    /\ OutChan_Rcv
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================