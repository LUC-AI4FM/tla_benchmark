------------------------------- MODULE MCSession6 -------------------------------
EXTENDS Session6, Naturals, TLC

(***************************************************************************)
(* Model-checking properties for the specification of Session6.            *)
(* Session6 is assumed to declare a constant N, the variables x, i and pc,  *)
(* and the operators Init, Next and Spec. It computes the square of N in   *)
(* x by repeated addition:                                                  *)
(*   a: while (i < N) { b: x := x + N; i := i + 1 }                         *)
(* This module defines no transition system or temporal specification of   *)
(* its own. It contains no fairness conditions, proofs or PlusCal          *)
(* algorithm.                                                               *)
(***************************************************************************)

(***************************************************************************)
(* Concrete constant set. It is used in place of Nat so that TLC can       *)
(* enumerate the values.                                                    *)
(***************************************************************************)
MCNat == 0 .. 100

(***************************************************************************)
(* Partial correctness: when the algorithm is done, x is the square of N.  *)
(***************************************************************************)
PartialCorrectness ==
    pc = "Done" => x = N * N

(***************************************************************************)
(* Typing invariant over the state variables.                              *)
(***************************************************************************)
TypeOK ==
    /\ x \in Nat
    /\ i \in Nat
    /\ pc \in {"a", "b", "Done"}

(***************************************************************************)
(* Stronger invariant. It gives the values of x and i at each control      *)
(* location and so characterizes the reachable states.                     *)
(***************************************************************************)
Inv ==
    /\ TypeOK
    /\ pc = "a"    => /\ i \in 0 .. N
                      /\ x = i * N
    /\ pc = "b"    => /\ i \in 0 .. (N - 1)
                      /\ x = i * N
    /\ pc = "Done" => /\ i = N
                      /\ x = N * N

=============================================================================