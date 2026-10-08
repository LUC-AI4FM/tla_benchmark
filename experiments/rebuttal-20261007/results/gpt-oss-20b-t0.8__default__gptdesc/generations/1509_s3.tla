----------------------------- MODULE RecSys -----------------------------
EXTENDS Naturals

VARIABLE x

(* Recursive function-like operator F over the set {1,2,3,4,5}. *)
F == [i \in 1..5 |-> 
          IF i = 1 THEN 2
          ELSE IF i = 3 THEN 4
          ELSE LET g == F IN g[i-1] + 1]

(* Indexed action N(i) for i ∈ {1,2,3}. *)
N(i) == /\ i \in 1..3
        /\ x' = i

(* Initial condition on x. *)
Init == x = 1

(* Existentially quantified indexed action A. *)
A == \E i \in 1..3 : N(i)

(* Safety invariant relating x to values of F. *)
Inv == (x \in 1..5) => (x = F[x])

Spec == Init /\ [] [A]_x
============================================================================