------------------------------ MODULE MCSession11projimpl ------------------------------
EXTENDS Session11projimpl, Sequences, Naturals, TLC

(***************************************************************************)
(* Concrete constant substituted for the parameter Data of the            *)
(* underlying implementation module.  Spec and Data are inherited from    *)
(* Session11projimpl through EXTENDS.                                     *)
(***************************************************************************)
ConstData == {"d1", "d2"}

(***************************************************************************)
(* State constraint bounding the lengths of the message queues so the     *)
(* model is finite.                                                       *)
(***************************************************************************)
StateConstraint ==
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3
    /\ Len(NewValQueue) =< 3

(***************************************************************************)
(* Type-correctness predicate for the implementation state.               *)
(***************************************************************************)
ABE_TypeOK ==
    /\ AVar \in [val : Data, bit : {0, 1}]
    /\ BVar \in [val : Data, bit : {0, 1}]
    /\ AtoB \in Seq([val : Data, bit : {0, 1}])
    /\ BtoA \in Seq({0, 1})
    /\ NewValQueue \in Seq(Data)

(***************************************************************************)
(* If B holds an acknowledgment whose bit matches AVar.bit, then B has    *)
(* received the value A is currently sending.  This invariant can fail if *)
(* the environment proposes new values too quickly, because A may move on *)
(* to a new value before B's acknowledgment is processed.                 *)
(***************************************************************************)
Inv ==
    (BVar.bit = AVar.bit) => (BVar = AVar)

(***************************************************************************)
(* Helper predicate over sequences: consecutive elements are distinct.    *)
(***************************************************************************)
TwoValsSeq(s) ==
    \A i \in 1..(Len(s) - 1) : s[i] # s[i + 1]

(***************************************************************************)
(* The high-level specification property imported from Session11projspec. *)
(***************************************************************************)
ABESpec == INSTANCE Session11projspec

ABESpecProperty == ABESpec!Spec
=============================================================================