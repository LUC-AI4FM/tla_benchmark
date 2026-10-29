---------------------------- MODULE InnerFIFO_ ----------------------------
(***************************************************************************)
(* A TLC-oriented version of the InnerFIFO specification.  The original    *)
(* specification used two INSTANCE statements of the Channel module.       *)
(* Here the channel operators are expanded manually and prefixed with      *)
(* InChan_ and OutChan_ for the input and output channels.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

(***************************************************************************)
(* Expanded operators of the input channel (Channel with Data <- Message,  *)
(* chan <- in).                                                            *)
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

(***************************************************************************)
(* Expanded operators of the output channel (Channel with Data <- Message, *)
(* chan <- out).                                                           *)
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

(***************************************************************************)
(* The inner FIFO specification.                                           *)
(***************************************************************************)
Init ==
    /\ InChan_Init
    /\ OutChan_Init
    /\ q = << >>

TypeInvariant ==
    /\ InChan_TypeInvariant
    /\ OutChan_TypeInvariant
    /\ q \in Seq(Message)

\* The sender sends a value on the input channel.
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

\* The receiver receives a message on the output channel.
RRcv ==
    /\ OutChan_Rcv
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================