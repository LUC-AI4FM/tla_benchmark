---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* TLC-specific wrapper for model checking the inner FIFO specification.   *)
(*                                                                         *)
(* The inner FIFO specification has an unbounded state space: the queue q *)
(* can grow arbitrarily large. To make model checking with TLC feasible    *)
(* without modifying the underlying specification, this module adds a     *)
(* constant bound qLen and a state constraint qConstraint. qConstraint     *)
(* holds only in states where the length of q is at most qLen.            *)
(*                                                                         *)
(* Use it from a TLC configuration file:                                   *)
(*                                                                         *)
(*     CONSTRAINT qConstraint                                              *)
(*                                                                         *)
(* The inner FIFO is reproduced below so that the module parses on its     *)
(* own. In the original setting this module simply does                   *)
(* "EXTENDS InnerFIFO" and adds only qLen and qConstraint.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Message,   \* the set of messages that can be sent
          qLen       \* TLC-only bound on the length of the queue

ASSUME qLen \in Nat

VARIABLES in, out, q

vars == <<in, out, q>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Inner FIFO specification (asynchronous channel interface).              *)
(***************************************************************************)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

TypeInvariant ==
    /\ in  \in ChanType
    /\ out \in ChanType
    /\ q   \in Seq(Message)

Init ==
    /\ in  \in ChanType
    /\ in.ack = in.rdy
    /\ out \in ChanType
    /\ out.ack = out.rdy
    /\ q = << >>

\* The sender places message msg on channel in.
SSend(msg) ==
    /\ in.rdy = in.ack
    /\ in' = [in EXCEPT !.val = msg, !.rdy = 1 - @]
    /\ UNCHANGED <<out, q>>

\* The buffer receives a message from channel in and appends it to q.
BufRcv ==
    /\ in.rdy # in.ack
    /\ q' = Append(q, in.val)
    /\ in' = [in EXCEPT !.ack = 1 - @]
    /\ UNCHANGED out

\* The buffer sends the head of q on channel out.
BufSend ==
    /\ q # << >>
    /\ out.rdy = out.ack
    /\ out' = [out EXCEPT !.val = Head(q), !.rdy = 1 - @]
    /\ q' = Tail(q)
    /\ UNCHANGED in

\* The receiver takes the message from channel out.
RRcv ==
    /\ out.rdy # out.ack
    /\ out' = [out EXCEPT !.ack = 1 - @]
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* TLC state constraint: bound the length of the queue q by qLen.          *)
(***************************************************************************)
qConstraint == Len(q) \leq qLen

THEOREM Spec => []TypeInvariant
=============================================================================