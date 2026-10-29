---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* TLC-specific wrapper for model checking the inner FIFO specification.  *)
(*                                                                         *)
(* The underlying FIFO specification has an unbounded state space because *)
(* the queue q can grow arbitrarily large. This module adds a constant     *)
(* bound qLen and a state constraint qConstraint that limits the length of *)
(* q to at most qLen. qConstraint is meant to be named in a TLC           *)
(* configuration file, for example:                                        *)
(*                                                                         *)
(*     CONSTRAINT qConstraint                                              *)
(*                                                                         *)
(* The standard construction is "EXTENDS InnerFIFO". So that this module  *)
(* parses on its own, the inner FIFO definitions are inlined below without *)
(* any change to their meaning. The only new content is qLen and          *)
(* qConstraint.                                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message      \* The set of messages carried by the FIFO
CONSTANT qLen         \* TLC bound on the length of the internal queue

ASSUME qLen \in Nat

VARIABLES in, out, q

vars == <<in, out, q>>

(***************************************************************************)
(* Inlined asynchronous Channel operators, parameterized by the channel.  *)
(***************************************************************************)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in ChanType
               /\ c.rdy = c.ack

\* Send(d, c, c2): send d on channel c, where c2 is the primed value of c.
ChanSend(d, c, c2) == /\ c.rdy = c.ack
                      /\ c2 = [c EXCEPT !.val = d, !.rdy = 1 - @]

\* Rcv(c, c2): acknowledge receipt on channel c.
ChanRcv(c, c2) == /\ c.rdy # c.ack
                  /\ c2 = [c EXCEPT !.ack = 1 - @]

(***************************************************************************)
(* Inner FIFO specification (unchanged semantics).                        *)
(***************************************************************************)
TypeInvariant == /\ in \in ChanType
                 /\ out \in ChanType
                 /\ q \in Seq(Message)

Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

SSend(msg) == /\ ChanSend(msg, in, in')    \* Sender sends msg on in
              /\ UNCHANGED <<out, q>>

BufRcv == /\ ChanRcv(in, in')              \* Buffer receives from in
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

BufSend == /\ q # << >>                    \* Buffer sends head of q on out
           /\ ChanSend(Head(q), out, out')
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ ChanRcv(out, out')              \* Receiver receives from out
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* TLC state constraint: bound the queue length to make the state space   *)
(* finite.                                                                  *)
(***************************************************************************)
qConstraint == Len(q) <= qLen

=============================================================================