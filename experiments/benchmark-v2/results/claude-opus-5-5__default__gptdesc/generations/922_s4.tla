---------------------------- MODULE InnerFIFO --------------------------------
(***************************************************************************)
(* TLC-oriented version of the InnerFIFO specification. The original      *)
(* version uses INSTANCE statements to import the Channel module for the   *)
(* input and output channels. Here those instantiated operators are        *)
(* expanded by hand into operators prefixed with InChan_ and OutChan_.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Expansion of  InChan == INSTANCE Channel WITH Data <- Message,          *)
(*                                                chan <- in               *)
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
(* Expansion of  OutChan == INSTANCE Channel WITH Data <- Message,         *)
(*                                                 chan <- out             *)
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

SSend(msg) ==                 \* Send msg on channel in.
    /\ InChan_Send(msg)
    /\ UNCHANGED <<out, q>>

BufRcv ==                     \* Receive message from channel in
    /\ InChan_Rcv             \* and append it to the tail of q.
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

BufSend ==                    \* Enabled only if q is nonempty.
    /\ q # << >>              \* Send Head(q) on channel out
    /\ OutChan_Send(Head(q))  \* and remove it from q.
    /\ q' = Tail(q)
    /\ UNCHANGED in

RRcv ==                       \* Receive message from channel out.
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