---------------------------- MODULE MCSession11a ----------------------------
(***************************************************************************)
(* Model-checking companion for Session11a.  Self-contained: the state     *)
(* structure that would be imported from Session11a (AVar, BVar, Msgs) is  *)
(* reproduced here so the module parses on its own.  The module supplies   *)
(* a concrete data set and two state predicates: TypeOK and Inv.           *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Concrete constant data set supplied for model checking.                 *)
(***************************************************************************)
MCData == {"d1", "d2", "d3"}

Data == MCData

(***************************************************************************)
(* Message records: a data value paired with an alternating bit.           *)
(***************************************************************************)
Msgs == [data : Data, bit : {0, 1}]

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* State structure of Session11a, reproduced so the module is complete.    *)
(***************************************************************************)
Init ==
    /\ AVar \in [data : Data, bit : {0}]
    /\ BVar = AVar

\* A sends a new value with a flipped bit once B has caught up.
A ==
    /\ AVar = BVar
    /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
    /\ UNCHANGED BVar

\* B receives the value currently held by A.
B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type-correctness: AVar and BVar are elements of Msgs.                   *)
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