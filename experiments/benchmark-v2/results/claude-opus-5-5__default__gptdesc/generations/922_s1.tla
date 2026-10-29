---------------------------- MODULE InnerFIFO_ ----------------------------
(***************************************************************************)
(* TLC-oriented version of the InnerFIFO specification.  The original      *)
(* specification used                                                       *)
(*                                                                          *)
(*    InChan  == INSTANCE Channel WITH Data <- Message, chan <- in          *)
(*    OutChan == INSTANCE Channel WITH Data <- Message, chan <- out         *)
(*                                                                          *)
(* Here those instantiated operators are expanded by hand into the          *)
(* prefixed operators InChan_xxx and OutChan_xxx.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Expansion of InChan == INSTANCE Channel WITH Data <- Message,           *)
(*                                              chan <- in                 *)
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

InChan_Next ==
    (\E d \in Message : InChan_Send(d)) \/ InChan_Rcv

InChan_Spec == InChan_Init /\ [][InChan_Next]_in

---------------------------------------------------------------------------
(***************************************************************************)
(* Expansion of OutChan == INSTANCE Channel WITH Data <- Message,          *)
(*                                               chan <- out               *)
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

OutChan_Next ==
    (\E d \in Message : OutChan_Send(d)) \/ OutChan_Rcv

OutChan_Spec == OutChan_Init /\ [][OutChan_Next]_out

---------------------------------------------------------------------------
(***************************************************************************)
(* The inner FIFO buffer.                                                  *)
(***************************************************************************)
Init ==
    /\ InChan_Init
    /\ OutChan_Init
    /\ q = << >>

TypeInvariant ==
    /\ InChan_TypeInvariant
    /\ OutChan_TypeInvariant
    /\ q \in Seq(Message)

\* The sender sends a message msg on the input channel.
SSend(msg) ==
    /\ InChan_Send(msg)
    /\ UNCHANGED <<out, q>>

\* The buffer receives a message from the input channel and appends it to q.
BufRcv ==
    /\ InChan_Rcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

\* The buffer sends the message at the head of q on the output channel.
BufSend ==
    /\ q # << >>
    /\ OutChan_Send(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in

\* The receiver receives a message from the output channel.
RRcv ==
    /\ OutChan_Rcv
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================