---- MODULE InitStateGeneration ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

\* Assignment followed by a tautological disjunction
Init1 == x = 1 /\ (TRUE \/ TRUE)

\* Tautological disjunction followed by an assignment
Init2 == (TRUE \/ TRUE) /\ x = 2

\* Double-negated tautology combined with an assignment
Init3 == (~~TRUE \/ ~~TRUE) /\ x = 3

\* Assignment followed by a double-negated tautology
Init4 == x = 4 /\ ~~(TRUE \/ TRUE)

\* Assignment combined with an unsatisfiable disjunction
Init5 == x = 5 /\ (FALSE \/ FALSE)

\* Unsatisfiable disjunction followed by an assignment
Init6 == (FALSE \/ ~TRUE) /\ x = 6

\* Nested disjunctions with mixed satisfiability
Init7 == x = 7 /\ ((FALSE \/ TRUE) \/ (TRUE \/ FALSE))

Init8 == ((FALSE \/ (TRUE \/ TRUE)) \/ FALSE) /\ x = 8

\* Assignment inside a disjunct, other disjunct unsatisfiable
Init9 == (x = 9 /\ FALSE) \/ (x = 10 /\ (TRUE \/ FALSE))

\* Assignment with a tautology referencing the variable after binding
Init10 == x = 11 /\ (x = 11 \/ x # 11)

\* Simple direct assignments
Init11 == x = 12

Init12 == x = 13

Init ==
    \/ Init1
    \/ Init2
    \/ Init3
    \/ Init4
    \/ Init5
    \/ Init6
    \/ Init7
    \/ Init8
    \/ Init9
    \/ Init10
    \/ Init11
    \/ Init12

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

\* Expected set of distinct initial states (5, 6, 9 are unsatisfiable)
ExpectedInitValues == {1, 2, 3, 4, 7, 8, 10, 11, 12, 13}

TypeOK == x \in ExpectedInitValues

====