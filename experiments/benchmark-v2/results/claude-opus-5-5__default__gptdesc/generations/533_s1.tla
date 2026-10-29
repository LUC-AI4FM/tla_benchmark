---------------------------- MODULE MCSession4 ----------------------------
(***************************************************************************)
(* Model-checking helper module for Session4.                              *)
(*                                                                         *)
(* It declares no variables, actions or temporal formulas of its own. Any  *)
(* behavior specification (Init, Next, Spec) and its properties come from  *)
(* the extended module Session4. This module only supplies constant-valued *)
(* definitions that a model can substitute for constants of Session4.      *)
(***************************************************************************)
EXTENDS Session4, Integers

(***************************************************************************)
(* A distinguished minimum integer value. It plays the role of "minus      *)
(* infinity" and is smaller than every value used in the test inputs below *)
(* (those values all lie in 1..10).                                         *)
(***************************************************************************)
MCMinValue == -1000

(***************************************************************************)
(* The set of all tuples (functions with domain 1..l) whose elements lie   *)
(* in the shifted range (l+1)..(2*l), for every length l from 0 to 5.      *)
(* For l = 0 this contributes the empty tuple, since 1..0 is empty.        *)
(***************************************************************************)
MCTupleSet == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=============================================================================