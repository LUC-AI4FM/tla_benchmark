---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* TLC-specific wrapper for model checking the inner FIFO specification.   *)
(*                                                                         *)
(* The inner FIFO specification has an unbounded state space, because the  *)
(* internal queue q can grow arbitrarily large. TLC therefore cannot       *)
(* enumerate all its reachable states. This module adds a constant bound   *)
(* qLen and a state constraint qConstraint that limits the length of q to  *)
(* at most qLen. qConstraint is meant to be named in the CONSTRAINT        *)
(* section of the TLC configuration file.                                  *)
(*                                                                         *)
(* The original wrapper would simply write EXTENDS InnerFIFO. Here the     *)
(* inner FIFO definitions (and the Channel definitions it uses) are        *)
(* written out inline, so the module parses on its own without changing    *)
(* the FIFO's behavior.                                                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Message      \* The set of messages carried by the FIFO
CONSTANT qLen         \* TLC bound on the length of the internal queue

ASSUME qLen \in Nat

VARIABLES in, out, q

vars == <<in, out, q>>

---------------------------------------------------------------------------
(* Asynchronous channel operators (in the style of module Channel).        *)

ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in ChanType
               /\ c.ack = c.rdy

ChanSend(c, cp, d) == /\ c.rdy = c.ack
                      /\ cp = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c, cp) == /\ c.rdy # c.ack
                  /\ cp = [c EXCEPT !.ack = 1 - @]

---------------------------------------------------------------------------
(* Inner FIFO specification.                                               *)

TypeInvariant == /\ in \in ChanType
                 /\ out \in ChanType
                 /\ q \in Seq(Message)

Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

\* The sender sends message msg on channel in.
SSend(msg) == /\ ChanSend(in, in', msg)
              /\ UNCHANGED <<out, q>>

\* The buffer receives a message from channel in and appends it to q.
BufRcv == /\ ChanRcv(in, in')
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

\* The buffer sends the head of q on channel out.
BufSend == /\ q # << >>
           /\ ChanSend(out, out', Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

\* The receiver receives a message from channel out.
RRcv == /\ ChanRcv(out, out')
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* TLC state constraint: restrict the queue length to at most qLen,        *)
(* which keeps the explored state space finite.                            *)

qConstraint == Len(q) <= qLen

=============================================================================