---------------------------- MODULE OpConstant ----------------------------
(***************************************************************************)
(* Shows how a higher-order constant operator can be passed in through the *)
(* model configuration and used to drive state transitions.                *)
(*                                                                         *)
(* Op is a constant operator of arity 1. The spec says nothing about what  *)
(* it does. The configuration file chooses its meaning with a line such as *)
(*                                                                         *)
(*     CONSTANT Op <- Forty2                                               *)
(*                                                                         *)
(* This replaces Op with the locally defined operator Forty2, so the       *)
(* behavior changes without editing the spec.                              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Op(_)        \* a higher-order (operator) constant, arity 1

VARIABLE x

(***************************************************************************)
(* A locally defined operator to substitute for Op in the configuration.   *)
(* It ignores its argument and returns the powerset of a fixed finite set. *)
(***************************************************************************)
Forty2(n) == SUBSET {4, 2}

Init == x = 0

(***************************************************************************)
(* The next value of x is drawn from the set Op(x).                        *)
(***************************************************************************)
Next == x' \in Op(x)

Spec == Init /\ [][Next]_x
=============================================================================