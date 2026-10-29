---------------------------- MODULE MCSession11a ----------------------------
(***************************************************************************)
(* Model-checking companion module for the Session11a specification.       *)
(* It supplies a concrete data set and two state predicates over AVar and  *)
(* BVar: a type-correctness condition and an invariant saying that equal   *)
(* bit fields imply equal message records.                                 *)
(*                                                                         *)
(* The state structure of Session11a is reproduced here (AVar, BVar, Msgs, *)
(* Init, Next, Spec) so the module is self-contained and parses under      *)
(* SANY on its own.                                                        *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Concrete constant data set used for model checking.                     *)
(***************************************************************************)
MCData == {"d1", "d2", "d3"}

Data == MCData

(***************************************************************************)
(* Messages are records carrying a data value and an alternating bit.      *)
(***************************************************************************)
Msgs == [data : Data, bit : {0, 1}]

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* Imported state structure (as in Session11a).                            *)
(***************************************************************************)
Init ==
    /\ AVar \in Msgs
    /\ BVar = AVar

\* A sends a new value with the flipped bit once B has caught up.
A ==
    /\ AVar = BVar
    /\ \E d \in Data :
          AVar' = [data |-> d, bit |-> 1 - AVar.bit]
    /\ UNCHANGED BVar

\* B receives the value currently held by A.
B ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type-correctness condition: AVar and BVar are elements of Msgs.         *)
(***************************************************************************)
TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs

(***************************************************************************)
(* Invariant: if the bit fields of AVar and BVar are equal, then the two   *)
(* message records are equal.                                              *)
(***************************************************************************)
Inv ==
    (AVar.bit = BVar.bit) => (AVar = BVar)

=============================================================================