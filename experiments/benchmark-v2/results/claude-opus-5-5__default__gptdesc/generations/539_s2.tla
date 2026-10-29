---------------------------- MODULE MCSession6func ----------------------------
(***************************************************************************)
(* Model-checking companion for the Session6func algorithm.                *)
(*                                                                         *)
(*   variables x = [k \in 0..n |-> 0], i = 0;                              *)
(*   a: while (i <= n) {                                                   *)
(*   b:   x[i] := i * i;                                                   *)
(*        i := i + 1;                                                      *)
(*      }                                                                  *)
(*                                                                         *)
(* The algorithm is restated here so that the module is self-contained.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT n

ASSUME NAssumption == n \in Nat

VARIABLES x, i, pc

vars == << x, i, pc >>

Init ==
    /\ x = [k \in 0..n |-> 0]
    /\ i = 0
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF i <= n
          THEN pc' = "b"
          ELSE pc' = "Done"
    /\ UNCHANGED << x, i >>

b ==
    /\ pc = "b"
    /\ x' = [x EXCEPT ![i] = i * i]
    /\ i' = i + 1
    /\ pc' = "a"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Postcondition: on termination, x holds the squares of 0..n *)
Correct ==
    pc = "Done" => \A j \in 0..n : x[j] = j * j

(* Typing invariant *)
TypeOK ==
    /\ n \in Nat
    /\ x \in [0..n -> Nat]
    /\ i \in 0..(n + 1)
    /\ pc \in {"a", "b", "Done"}

(* Stronger inductive invariant characterizing each control location *)
Inv ==
    /\ TypeOK
    /\ pc = "a" =>
         /\ i \in 0..(n + 1)
         /\ \A j \in 0..(i - 1) : x[j] = j * j
    /\ pc = "b" =>
         /\ i \in 0..n
         /\ \A j \in 0..(i - 1) : x[j] = j * j
    /\ pc = "Done" =>
         /\ i = n + 1
         /\ \A j \in 0..n : x[j] = j * j

THEOREM Spec => [](TypeOK /\ Inv /\ Correct)
=============================================================================