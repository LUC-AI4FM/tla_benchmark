---- MODULE InitStateTest ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

\* I1a: assigns x = 0, with a tautological disjunction as the second conjunct.
I1a == /\ x = 0
       /\ (1 = 1) \/ (2 = 2)

\* I1b: tautological disjunction placed first; TLC may generate the
\* state x = 1 twice (once for each true disjunct).
I1b == /\ (1 = 1) \/ (2 = 2)
       /\ x = 1

\* I1c: workaround using double negation of the tautological disjunction,
\* so TLC evaluates it as a single boolean rather than splitting it.
I1c == /\ ~~((1 = 1) \/ (2 = 2))
       /\ x = 2

\* I2: a false predicate prevents the assignment from succeeding.
I2 == /\ FALSE
      /\ x = 3

\* I3: a false predicate placed after the assignment prevents success.
I3 == /\ x = 4
      /\ 1 = 2

\* I4: assigns x = 5 or x = 6 through nested disjunctions.
I4 == \/ /\ TRUE
         /\ \/ x = 5
            \/ x = 6
      \/ /\ 1 = 2
         /\ x = 99

\* I5: simply assigns x = 7.
I5 == x = 7

Init == \/ I1a
        \/ I1b
        \/ I1c
        \/ I2
        \/ I3
        \/ I4
        \/ I5

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

====