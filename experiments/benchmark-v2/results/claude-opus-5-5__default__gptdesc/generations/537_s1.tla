---------------------------- MODULE MCSession6 ----------------------------
(***************************************************************************)
(* Model-checking properties for the squaring program of Session6.         *)
(* Session6's program is inlined below so that this module parses on its   *)
(* own. The program computes N*N by summing the first N odd numbers:       *)
(*                                                                         *)
(*     x := 0 ; i := 0 ;                                                   *)
(*  a: while (i < N) {                                                     *)
(*  b:    x := x + 2*i + 1 ; i := i + 1                                    *)
(*     }                                                                   *)
(*                                                                         *)
(* No fairness conditions are assumed.                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES x, i, pc

vars == << x, i, pc >>

(***************************************************************************)
(* Concrete constant set: a finite stand-in for Nat, so TLC can check the  *)
(* properties below.                                                       *)
(***************************************************************************)
MCNat == 0 .. (N * N)

Labels == {"a", "b", "Done"}

---------------------------------------------------------------------------
(* Transition system imported from Session6 *)

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

---------------------------------------------------------------------------
(* Properties *)

(* Partial correctness: at the final control location, x is the square *)
PartialCorrectness == (pc = "Done") => (x = N * N)

(* Typing invariant over the state variables *)
TypeOK == /\ x \in MCNat
          /\ i \in 0 .. N
          /\ pc \in Labels

(* Stronger reachable-state invariant: values of x and i at each location *)
Inv == /\ TypeOK
       /\ pc = "a"    => (x = i * i /\ i <= N)
       /\ pc = "b"    => (x = i * i /\ i < N)
       /\ pc = "Done" => (x = N * N /\ i = N)

THEOREM Spec => [](TypeOK /\ Inv /\ PartialCorrectness)
=============================================================================