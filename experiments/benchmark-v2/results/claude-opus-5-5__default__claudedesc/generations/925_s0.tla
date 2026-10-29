---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the InnerFIFOInstanced specification.        *)
(* The FIFO definitions are inlined so that this module parses on its own. *)
(* qConstraint bounds the internal queue q so that TLC can explore a       *)
(* finite state space.                                                     *)
(*                                                                         *)
(* Intended TLC configuration:                                             *)
(*   CONSTANTS Message = {m1, m2, m3}                                      *)
(*             qLen    = 3                                                 *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTRAINT    qConstraint                                             *)
(*   INVARIANT     TypeInvariant                                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Message, qLen

VARIABLES in, out, q

vars == <<in, out, q>>

(***************************************************************************)
(* Asynchronous channel record definitions (as in Channel module).         *)
(***************************************************************************)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

ChanInit(c) == /\ c \in ChanType
               /\ c.ack = c.rdy

ChanSend(c, d) == /\ c.rdy = c.ack
                  /\ c' = [c EXCEPT !.val = d, !.rdy = 1 - @]

ChanRcv(c) == /\ c.rdy # c.ack
              /\ c' = [c EXCEPT !.ack = 1 - @]

(***************************************************************************)
(* InnerFIFO specification with two channel instances: in and out.         *)
(***************************************************************************)
Init == /\ ChanInit(in)
        /\ ChanInit(out)
        /\ q = << >>

TypeInvariant == /\ in \in ChanType
                 /\ out \in ChanType
                 /\ q \in Seq(Message)

SSend(msg) == /\ ChanSend(in, msg)          \* environment sends msg on in
              /\ UNCHANGED <<out, q>>

BufRcv == /\ ChanRcv(in)                     \* buffer receives from in
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

BufSend == /\ q # << >>                      \* buffer sends head of q on out
           /\ ChanSend(out, Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ ChanRcv(out)                      \* receiver takes msg from out
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking constraint: bound the length of the internal queue.      *)
(***************************************************************************)
qConstraint == Len(q) <= qLen

THEOREM Spec => []TypeInvariant
=============================================================================