--------------------------- MODULE RandomSubsetSample ----------------------------
EXTENDS Naturals, FiniteSets, SetTheory

CONSTANTS S, RandomSubset

VARIABLE x

(*---------------------------------------------------------------------*)
(* Type invariant: RandomSubset is a subset of functions from S to 1..10 *)
TypeInv == RandomSubset \subseteq [s \in S |-> 1 .. 10]

(* The set of all functions from S to 1..10 *)
AllFuncs == [s \in S |-> 1 .. 10]

(*---------------------------------------------------------------------*)
Init ==
    /\ x \in AllFuncs
    /\ x \in RandomSubset

Next == (x' = x)

Inv == TRUE

Spec == Init /\ []Next /\ TypeInv

THEOREM InvHolds : Spec => [](Inv)
=============================================================================