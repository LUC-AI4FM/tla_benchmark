---- MODULE HigherOrderFilter ----

VARIABLES x

(*--algorithm HigherOrderFilter
variables x;

Init == x \in Filter({1, 2, 3, 4, 5}, (y \in Nat \cup {FALSE} => y > 1), (y \in Nat \cup {FALSE} => y % 2 = 1) /\ (TRUE))

Next == FALSE

Filter(S, UnaryPred, BinaryPred) ==
    { s \in S : UnaryPred(s) /\ BinaryPred(s) }

end algorithm *)
====