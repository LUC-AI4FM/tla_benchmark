---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* TLC-specific wrapper for the inner FIFO specification.                  *)
(*                                                                         *)
(* The FIFO spec has an unbounded state space because the queue q can grow *)
(* arbitrarily large. This module adds a constant bound qLen and a state   *)
(* constraint qConstraint that limits the length of q to at most qLen.     *)
(* A TLC configuration can then reference qConstraint as a CONSTRAINT,     *)
(* which gives TLC a finite state space without modifying the FIFO spec.   *)
(*                                                                         *)
(* The inner FIFO is written out here so that this module parses on its    *)
(* own.                                                                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

-----------------------------------------------------------------------------
(* The asynchronous channel interface, written inline.                     *)

ChanTypeInv(c) ==
    /\ c \in [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanSend(c, d) ==
    /\ c.rdy = c.ack
    /\ c' = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c) ==
    /\ c.rdy # c.ack
    /\ c' = [c EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------
(* The inner FIFO specification.                                           *)

Init ==
    /\ in \in [val : Message, rdy : {0, 1}, ack : {0, 1}]
    /\ in.ack = in.rdy
    /\ out \in [val : Message, rdy : {0, 1}, ack : {0, 1}]
    /\ out.ack = out.rdy
    /\ q = << >>

TypeInvariant ==
    /\ ChanTypeInv(in)
    /\ ChanTypeInv(out)
    /\ q \in Seq(Message)

SSend(msg) ==
    /\ ChanSend(in, msg)
    /\ UNCHANGED <<out, q>>

BufRcv ==
    /\ ChanRcv(in)
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

BufSend ==
    /\ q # << >>
    /\ ChanSend(out, Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in

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
(* The TLC-specific state constraint.                                      *)

CONSTANT qLen

qConstraint == Len(q) <= qLen
=============================================================================