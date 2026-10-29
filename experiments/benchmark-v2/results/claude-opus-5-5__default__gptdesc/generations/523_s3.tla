---------------------------- MODULE MCSession11projimpl ----------------------------
(***************************************************************************)
(* Model-checking module for the alternating-bit style session             *)
(* implementation Session11projimpl.  Init, Next and Spec are inherited    *)
(* from the extended module.  This module adds concrete constants, a       *)
(* state constraint bounding the queue lengths, a type-correctness         *)
(* predicate, an invariant relating A and B, a helper predicate over       *)
(* sequences, and the projected specification property to check.          *)
(***************************************************************************)
EXTENDS Session11projimpl, Naturals, Sequences, TLC

(***************************************************************************)
(* Concrete constants used to override the parameters of the model.        *)
(***************************************************************************)
MCData == {"d1", "d2"}

MaxQueueLen == 3

(***************************************************************************)
(* State constraint: bound the lengths of the message queues so that the   *)
(* state space is finite.                                                  *)
(***************************************************************************)
StateConstraint ==
    /\ Len(AtoB)        =< MaxQueueLen
    /\ Len(BtoA)        =< MaxQueueLen
    /\ Len(NewValQueue) =< MaxQueueLen

(***************************************************************************)
(* Type correctness of the implementation state.                           *)
(***************************************************************************)
ImplTypeOK ==
    /\ AVar \in [val : Data, bit : {0, 1}]
    /\ BVar \in [val : Data, bit : {0, 1}]
    /\ AtoB \in Seq(Data \X {0, 1})
    /\ BtoA \in Seq({0, 1})
    /\ NewValQueue \in Seq(Data)

(***************************************************************************)
(* Invariant relating A and B: whenever B holds an acknowledgment whose    *)
(* bit matches AVar.bit, B has received the value that A is sending.       *)
(*                                                                         *)
(* NOTE: This invariant may FAIL when the environment proposes new values  *)
(* too quickly (i.e., NewValQueue fills up and A moves on to a new value   *)
(* before B's acknowledgment of the previous one has been processed, so    *)
(* the bits can coincide while the values differ).                         *)
(***************************************************************************)
ABInv ==
    (BVar.bit = AVar.bit) => (BVar.val = AVar.val)

(***************************************************************************)
(* Helper predicate: the sequence s contains at most two distinct values.  *)
(***************************************************************************)
TwoValsSeq(s) ==
    \E v1, v2 \in Data :
        \A i \in 1..Len(s) : s[i] \in {v1, v2}

(***************************************************************************)
(* The projected high-level specification, imported from                   *)
(* Session11projspec, which the implementation should satisfy.             *)
(***************************************************************************)
ProjSpec == INSTANCE Session11projspec

ProjSpecProperty == ProjSpec!Spec

=============================================================================