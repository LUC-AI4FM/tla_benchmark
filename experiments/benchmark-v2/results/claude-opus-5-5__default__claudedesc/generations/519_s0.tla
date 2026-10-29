---------------------------- MODULE MC_Session11 ----------------------------
(***************************************************************************)
(* Model-checking configuration module for checking that the alternating   *)
(* bit protocol implementation (Session11c) refines the higher-level       *)
(* specification (Session11a) under a data refinement mapping.             *)
(*                                                                         *)
(* Session11c is assumed to declare CONSTANT Data, the VARIABLES AVar2,    *)
(* BVar2, AtoB, BtoA, and the operators Init, Next and Spec.               *)
(* Because they are inherited through EXTENDS, they are not redeclared     *)
(* here; MC_Init, MC_Next and MC_Spec refer to them for use in TLC.        *)
(***************************************************************************)
EXTENDS Session11c, Sequences, Naturals, TLC

(***************************************************************************)
(* Model values used to instantiate the constant Data.                    *)
(***************************************************************************)
CONSTANTS d1, d2, d3

(***************************************************************************)
(* Concrete set of three message payloads.  In the TLC configuration this  *)
(* is used as:   CONSTANT Data <- const_Data                               *)
(***************************************************************************)
const_Data == {d1, d2, d3}

(***************************************************************************)
(* Initial predicate, next-state relation and specification of the         *)
(* implementation, taken from Session11c.                                  *)
(***************************************************************************)
MC_Init == Init

MC_Next == Next

MC_Spec == Spec

(***************************************************************************)
(* State constraint: at most three messages in each channel.              *)
(***************************************************************************)
StateConstraint ==
    /\ Len(AtoB) <= 3
    /\ Len(BtoA) <= 3

(***************************************************************************)
(* Type invariant.  AVar2 and BVar2 hold <<data, bit>> tuples, AtoB is a   *)
(* sequence of such messages and BtoA is a sequence of acknowledgment      *)
(* bits.                                                                   *)
(***************************************************************************)
AB2_TypeOK ==
    /\ AVar2 \in Data \X {0, 1}
    /\ BVar2 \in Data \X {0, 1}
    /\ AtoB \in Seq(Data \X {0, 1})
    /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* Refinement mapping: convert the tuple-based representation into the     *)
(* record-based representation used by the abstract specification.        *)
(***************************************************************************)
AVar_Impl == [data |-> AVar2[1], bit |-> AVar2[2]]

BVar_Impl == [data |-> BVar2[1], bit |-> BVar2[2]]

(***************************************************************************)
(* Instance of the abstract specification under the refinement mapping.   *)
(* The constant Data is substituted implicitly by the same-named constant. *)
(***************************************************************************)
ABS == INSTANCE Session11a WITH AVar <- AVar_Impl, BVar <- BVar_Impl

(***************************************************************************)
(* Refinement property: every behavior of Session11c satisfies the         *)
(* temporal specification of Session11a under the substitution above.     *)
(***************************************************************************)
ABSpecProperty == ABS!Spec

(***************************************************************************)
(* Theorems checked by TLC.                                               *)
(***************************************************************************)
THEOREM MC_Spec => []AB2_TypeOK
THEOREM MC_Spec => ABSpecProperty

=============================================================================