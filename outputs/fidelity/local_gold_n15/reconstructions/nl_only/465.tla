---- MODULE SetConstructorTest ----

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    A, B, C \* Example sets for testing

VARIABLES x

Init == x = TRUE

Next == UNCHANGED x

Inv ==
    LET 
        S1 == {y \in BOOLEAN | y}
        S2 == {z \in {TRUE} : z}
        S3 == [A -> B]
        S4 == [a \in A, b \in B -> c \in C: <<a, b>> -> c]
        S5 == UNION {[a \in A -> {b}] | a \in A}
        S6 == SUBSET BOOLEAN
        S7 == CartesianProduct(A, B)
        S8 == DOMAIN [A -> B]
        S9 == {f \in [A -> B] : f[a] = b FORALL a \in A}
        S10 == Cardinality(S1) = 1
    IN
        /\ Assert(Cardinality(S1) = 1, "Cardinality of S1 should be 1")
        /\ Assert(Cardinality(S2) = 1, "Cardinality of S2 should be 1")
        /\ Assert(Cardinality(S3) = Cardinality(A) ** Cardinality(B), "Cardinality of S3 should match A and B sizes")
        /\ Assert(Cardinality(S4) = Cardinality(A) ** Cardinality(B) ** Cardinality(C), "Cardinality of S4 should match A, B, and C sizes")
        /\ Assert(Cardinality(S5) = Cardinality(A), "Cardinality of S5 should match A size")
        /\ Assert(Cardinality(S6) = 2 ** Cardinality(BOOLEAN), "Cardinality of S6 should be 2^|BOOLEAN|")
        /\ Assert(Cardinality(S7) = Cardinality(A) * Cardinality(B), "Cardinality of S7 should match Cartesian product of A and B sizes")
        /\ Assert(Cardinality(S8) = Cardinality(A), "Cardinality of S8 should match A size")
        /\ Assert(Cardinality(S9) <= Cardinality([A -> {b}]), "Cardinality of S9 should be less than or equal to functions mapping A to a single element in B")
        /\ Assert(S10, "S10 assertion failed")

Spec == Init /\ [][Next]_<<x>> /\ WF_next(<<x>>) /\ Inv
========================================