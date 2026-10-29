------------------------------- MODULE RecFunc -------------------------------
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x

vars == << x >>

-----------------------------------------------------------------------------
(* Recursively defined function over the set {1,2,3,4,5}: factorial.       *)
F[i \in {1, 2, 3, 4, 5}] == IF i = 1 THEN 1 ELSE i * F[i - 1]

(* Action-valued function indexed by {1,2,3}.                               *)
N[i \in {1, 2, 3}] == x' = F[i + 2]

-----------------------------------------------------------------------------
Init == x = F[1]

Next == \E i \in {1, 2, 3} : N[i]

Spec == Init /\ [][Next]_x

-----------------------------------------------------------------------------
(* Invariant: x is always one of the values of F.                           *)
Inv == x \in {F[j] : j \in {1, 2, 3, 4, 5}}

TypeOK == x \in Nat

THEOREM Spec => [](Inv /\ TypeOK)
=============================================================================