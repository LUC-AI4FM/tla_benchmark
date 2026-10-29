---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* TLC wrapper for the inner FIFO specification.                           *)
(*                                                                         *)
(* The inner FIFO spec has an unbounded state space, because the queue q   *)
(* can grow arbitrarily large.  To model check it with TLC, this module    *)
(* adds a constant bound qLen and a state constraint qConstraint that      *)
(* limits the length of q to at most qLen.  The constraint is meant to be  *)
(* named in the TLC configuration file, for example:                       *)
(*                                                                         *)
(*     CONSTRAINT qConstraint                                              *)
(*                                                                         *)
(* The original wrapper would simply write EXTENDS InnerFIFO.  So that     *)
(* this module parses on its own with SANY, the inner FIFO definitions are *)
(* reproduced below without any change to their behavior.  The only        *)
(* addition is the bound qLen and the predicate qConstraint at the end.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

-----------------------------------------------------------------------------
(*************************** Inner FIFO (unchanged) ************************)

ChanTypeInv(chan) ==
    chan \in [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(chan) ==
    /\ chan.val \in Message
    /\ chan.rdy \in {0, 1}
    /\ chan.ack = chan.rdy

InSend(d) ==
    /\ in.rdy = in.ack
    /\ in' = [in EXCEPT !.val = d, !.rdy = 1 - @]

InRcv ==
    /\ in.rdy # in.ack
    /\ in' = [in EXCEPT !.ack = 1 - @]

OutSend(d) ==
    /\ out.rdy = out.ack
    /\ out' = [out EXCEPT !.val = d, !.rdy = 1 - @]

OutRcv ==
    /\ out.rdy # out.ack
    /\ out' = [out EXCEPT !.ack = 1 - @]

Init ==
    /\ ChanInit(in)
    /\ ChanInit(out)
    /\ q = << >>

TypeInvariant ==
    /\ ChanTypeInv(in)
    /\ ChanTypeInv(out)
    /\ q \in Seq(Message)

SSend(msg) ==
    /\ InSend(msg)
    /\ UNCHANGED <<out, q>>

BufRcv ==
    /\ InRcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED out

BufSend ==
    /\ q # << >>
    /\ OutSend(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in

RRcv ==
    /\ OutRcv
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

vars == <<in, out, q>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*************************** TLC state constraint **************************)

CONSTANT qLen

ASSUME qLen \in Nat

qConstraint == Len(q) \leq qLen

=============================================================================