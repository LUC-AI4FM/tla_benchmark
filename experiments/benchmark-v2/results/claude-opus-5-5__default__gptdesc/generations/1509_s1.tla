---------------------------- MODULE RecFunSpec ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

(* Recursive function definition over the domain {1,2,3,4,5}. *)
F[i \in {1,2,3,4,5}] == IF i = 1 THEN 1 ELSE F[i-1] + i

(* Indexed action operator, indexed by {1,2,3}. *)
N(i) == x' = F[i]

Init == x = F[1]

Next == \E i \in {1,2,3} : N(i)

Spec == Init /\ [][Next]_x

(* Type invariant. *)
TypeOK == x \in Nat

(* Invariant: x is always one of the values of F over {1,2,3}. *)
Inv == \E i \in {1,2,3} : x = F[i]

(* Weaker invariant: x is in the range of F. *)
InvRange == x \in {F[i] : i \in {1,2,3,4,5}}

THEOREM Spec => [](TypeOK /\ Inv /\ InvRange)
=============================================================================