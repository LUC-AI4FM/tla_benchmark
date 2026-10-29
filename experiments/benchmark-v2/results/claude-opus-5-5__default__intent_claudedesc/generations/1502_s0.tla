------------------------- MODULE OperatorConstantDemo -------------------------
(***************************************************************************)
(* Demonstrates passing an operator as a CONSTANT and overriding it in     *)
(* the model configuration. The spec's behavior is fully determined by     *)
(* the configured operator Op, so it can be changed without editing the   *)
(* spec.                                                                   *)
(*                                                                         *)
(* Example configuration file (OperatorConstantDemo.cfg):                  *)
(*                                                                         *)
(*     INIT Init                                                           *)
(*     NEXT Next                                                           *)
(*     CONSTANT Op <- LocalOp                                              *)
(*                                                                         *)
(* The line "CONSTANT Op <- LocalOp" substitutes the operator LocalOp,     *)
(* defined below, for the higher-order constant Op.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Op(_)    \* A constant operator of arity 1, supplied by the model.

VARIABLE x

vars == << x >>

(***************************************************************************)
(* A locally defined operator. It ignores its argument and returns the     *)
(* powerset of a fixed finite set. It can be substituted for Op in the     *)
(* configuration file.                                                     *)
(***************************************************************************)
FixedSet == {1, 2, 3}

LocalOp(a) == SUBSET FixedSet

Init == x = 0

(***************************************************************************)
(* The next value of x is any element of the set Op(x).                    *)
(***************************************************************************)
Next == x' \in Op(x)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* With Op <- LocalOp, every value of x after the initial state is a       *)
(* subset of FixedSet. This is shown for illustration only; it is not      *)
(* required to be checked.                                                 *)
(***************************************************************************)
TypeOKUnderLocalOp == x = 0 \/ x \subseteq FixedSet

===============================================================================