------------------------------ MODULE SmallSystem ------------------------------
EXTENDS Integers

VARIABLE x

(* Recursive function-like operator F over {1,2,3,4,5} *)
F(i) == IF i = 5 THEN 1 ELSE F(i + 1)

(* Indexed action N over {1,2,3} *)
N(i) == /\ i \in 1..3
        /\ x' = ((x + i - 1) Mod 5) + 1

(* Initial condition *)
Init == x = 1

(* Step action: existentially quantified indexed action under stuttering *)
Step == EXISTS i \in 1..3 : N(i)

Spec == Init /\ [] Step

Inv == x \in 1..5

=============================================================================