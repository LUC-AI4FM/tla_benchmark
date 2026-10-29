---------------------------- MODULE RecursiveFcn ----------------------------
EXTENDS Naturals

VARIABLE x

vars == x

(* Recursively defined function over {1,2,3,4,5} *)
F[i \in {1,2,3,4,5}] == IF i = 1 THEN 1 ELSE F[i-1] + i

(* Indexed action-style operator over {1,2,3} *)
N[i \in {1,2,3}] == x' = F[i]

Init == x = F[1]

Next == \E i \in {1,2,3} : N[i]

Spec == Init /\ [][Next]_x

(* Invariant relating x to the values of F *)
Inv == \E i \in {1,2,3,4,5} : x = F[i]

TypeOK == x \in Nat

THEOREM Spec => []Inv
=============================================================================