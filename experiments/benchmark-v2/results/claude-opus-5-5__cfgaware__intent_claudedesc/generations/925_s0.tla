---------------------------- MODULE FIFOQueue ----------------------------
(***************************************************************************)
(* A FIFO queue. Items are added at the back with Enqueue and removed     *)
(* from the front with Dequeue, so they leave in the order they arrived.  *)
(*                                                                         *)
(* The core specification puts no bound on the queue length. For model    *)
(* checking, the state constraint qConstraint limits the explored states  *)
(* to those whose queue length is at most qLen. qLen is set from outside, *)
(* in the model-checking configuration.                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Message,  \* The set of items that can be enqueued
          qLen      \* Maximum queue length explored by the model checker

ASSUME qLen \in Nat

VARIABLE q          \* The queue contents; the front of the queue is Head(q)

vars == << q >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Core queue specification                                               *)
(***************************************************************************)

Init == q = << >>

\* Add an item m to the back of the queue.
Enqueue(m) == q' = Append(q, m)

\* Remove the item at the front of the queue (the oldest item).
Dequeue == /\ q # << >>
           /\ q' = Tail(q)

Next == \/ \E m \in Message : Enqueue(m)
        \/ Dequeue

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                 *)
(***************************************************************************)

\* The queue is always a finite sequence of valid messages.
TypeInvariant == q \in Seq(Message)

\* Every step preserves the order and contents of the queue. A step either
\* adds exactly one item at the back, leaving the existing items unchanged
\* and in the same order, or removes exactly the front item and leaves the
\* rest unchanged. As a result, nothing is lost, corrupted, duplicated, or
\* reordered, and items are removed in the order they were added.
FIFOStep ==
    \/ \E m \in Message : q' = Append(q, m)
    \/ /\ q # << >>
       /\ q' = Tail(q)

FIFOProperty == [][FIFOStep]_vars

THEOREM Spec => []TypeInvariant /\ FIFOProperty

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking support                                                 *)
(***************************************************************************)

\* State constraint: limit exploration to queues of length at most qLen.
qConstraint == Len(q) <= qLen

=============================================================================