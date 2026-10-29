---------------------------- MODULE MCSession6func ----------------------------
(***************************************************************************)
(* Model-checking companion for the Session6func algorithm.  The          *)
(* algorithm fills a function x with the squares of the indices 0..n:     *)
(*                                                                         *)
(*   variables x = [j \in 0..n |-> 0], i = 0;                              *)
(*   a: while (i <= n) {                                                   *)
(*   b:   x[i] := i * i;                                                   *)
(*        i := i + 1                                                       *)
(*      }                                                                  *)
(*                                                                         *)
(* The algorithm is restated here so that the module stands alone.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

-----------------------------------------------------------------------------
(* Algorithm *)

Init == /\ n \in 0..N
        /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i <= n
           THEN pc' = "b"
           ELSE pc' = "Done"
     /\ UNCHANGED << n, x, i >>

b == /\ pc = "b"
     /\ x' = [x EXCEPT ![i] = i * i]
     /\ i' = i + 1
     /\ pc' = "a"
     /\ UNCHANGED n

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Properties checked by the model *)

\* Postcondition: on termination, x holds the square of every index.
Correct == pc = "Done" => \A j \in 0..n : x[j] = j * j

\* Typing invariant.
TypeOK == /\ n \in Nat
          /\ x \in [0..n -> Nat]
          /\ i \in 0..(n + 1)
          /\ pc \in {"a", "b", "Done"}

\* Stronger invariant that describes every reachable state.
Inv == /\ TypeOK
       /\ \A j \in 0..(i - 1) : x[j] = j * j
       /\ pc = "a"    => i \in 0..(n + 1)
       /\ pc = "b"    => i \in 0..n
       /\ pc = "Done" => i = n + 1

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []Correct
THEOREM Spec => Termination
=============================================================================