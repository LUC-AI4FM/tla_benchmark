------------------------- MODULE MCSession11projimpl -------------------------
(***************************************************************************)
(* Model-checking module for the alternating-bit style session             *)
(* implementation Session11projimpl.  It supplies concrete constants, a    *)
(* state constraint bounding the queues AtoB, BtoA and NewValQueue, a      *)
(* type-correctness predicate for the implementation state, an invariant   *)
(* relating A and B, a helper predicate on sequences, and the high-level   *)
(* specification of Session11projspec as a property to be checked.        *)
(***************************************************************************)
EXTENDS Session11projimpl, Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Concrete constants used by the model.  d1 and d2 are to be instantiated *)
(* as model values, and MCData is substituted for the constant Data.       *)
(***************************************************************************)
CONSTANTS d1, d2, MaxQLen

MCData == {d1, d2}

ASSUME MaxQLen \in Nat

(***************************************************************************)
(* State constraint: bound the lengths of the message queues so that the   *)
(* state space is finite.                                                  *)
(***************************************************************************)
StateConstraint ==
    /\ Len(AtoB)        =< MaxQLen
    /\ Len(BtoA)        =< MaxQLen
    /\ Len(NewValQueue) =< MaxQLen

(***************************************************************************)
(* Type-correctness predicate for the implementation state.                *)
(***************************************************************************)
Msg == [val : Data, bit : {0, 1}]

TypeOKImpl ==
    /\ AVar        \in Msg
    /\ BVar        \in Msg
    /\ AtoB        \in Seq(Msg)
    /\ BtoA        \in Seq({0, 1})
    /\ NewValQueue \in Seq(Data)

(***************************************************************************)
(* Invariant relating A and B: when B holds a value whose bit matches      *)
(* AVar.bit (i.e., B is in a position to acknowledge A's current value),   *)
(* B must hold the same value as A.                                        *)
(*                                                                         *)
(* NOTE: This invariant may fail.  If the environment proposes new values  *)
(* too quickly (enqueuing them on NewValQueue before the previous value    *)
(* has been acknowledged), A may move on to a new value whose bit happens  *)
(* to coincide with that of a stale value still held by B, so B's bit      *)
(* matches AVar.bit while BVar.val differs from AVar.val.                  *)
(***************************************************************************)
ABInv ==
    (BVar.bit = AVar.bit) => (BVar = AVar)

(***************************************************************************)
(* Helper predicate: the sequence s contains at most two distinct values.  *)
(***************************************************************************)
TwoValsSeq(s) ==
    Cardinality({s[i] : i \in DOMAIN s}) =< 2

(***************************************************************************)
(* Model-checking aliases for the implementation's specification.          *)
(***************************************************************************)
MCInit == Init

MCNext == Next

MCSpec == Spec

(***************************************************************************)
(* The high-level specification, imported from Session11projspec, which    *)
(* the implementation is checked to implement.                             *)
(***************************************************************************)
SP == INSTANCE Session11projspec

SpecProperty == SP!Spec

THEOREM MCSpec => [](TypeOKImpl)
THEOREM MCSpec => SpecProperty
=============================================================================