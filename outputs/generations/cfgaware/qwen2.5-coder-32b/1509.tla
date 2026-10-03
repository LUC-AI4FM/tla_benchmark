------------------------------- MODULE SmallSystem -------------------------------

CONSTANTS
    F, N, Spec, Inv

VARIABLES x

(*--algorithm SmallSystem
variables x \in {1,2,3,4,5};

F == [n \in {1,2,3,4,5} |-> IF n = 1 THEN 2 ELSE IF n = 2 THEN 3 ELSE IF n = 3 THEN 4 ELSE IF n = 4 THEN 5 ELSE 1]

N ==
    [1 |-> (x' \in {1,2}),
     2 |-> (x' \in {2,3}),
     3 |-> (x' \in {3,4})]

Spec == 
    /\ x \in {1,2,3,4,5}
    /\ [][\E i \in {1,2,3} : N[i]]_<<x>>

Inv ==
    F[x] = x + 1

end algorithm *)
=============================================================================