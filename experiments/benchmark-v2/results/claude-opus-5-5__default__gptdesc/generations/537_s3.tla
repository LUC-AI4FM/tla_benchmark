---------------------------- MODULE MCSession6 ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES x, i, pc

vars == << x, i, pc >>

(***************************************************************************)
(* Transition system corresponding to the imported Session6 algorithm,    *)
(* which computes the square of N by summing odd numbers:                 *)
(*   x := 0; i := 0;                                                       *)
(*   a: while (i < N) { b: x := x + 2*i + 1; i := i + 1 }                  *)
(***************************************************************************)

Init == /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < N
           THEN pc' = "b"
           ELSE pc' = "Done"
     /\ UNCHANGED << x, i >>

b == /\ pc = "b"
     /\ x' = x + 2 * i + 1
     /\ i' = i + 1
     /\ pc' = "a"

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Concrete constant set used for model checking (overrides Nat).          *)
(***************************************************************************)
MCNat == 0 .. 10

(***************************************************************************)
(* Partial correctness: on termination, x holds the square of N.           *)
(***************************************************************************)
PartialCorrectness == pc = "Done" => x = N * N

(***************************************************************************)
(* Typing invariant.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"a", "b", "Done"}

(***************************************************************************)
(* Stronger inductive invariant characterizing x and i at each location.   *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ pc = "a"    => /\ i \in 0 .. N
                         /\ x = i * i
       /\ pc = "b"    => /\ i \in 0 .. (N - 1)
                         /\ i < N
                         /\ x = i * i
       /\ pc = "Done" => /\ i = N
                         /\ x = N * N

THEOREM Spec => [](TypeOK /\ Inv /\ PartialCorrectness)
=============================================================================