---------------------------- MODULE Addition ----------------------------
EXTENDS Naturals

CONSTANTS a, b

ASSUME ConstantsAreNaturals == a \in Nat /\ b \in Nat

Add(x, y) == x + y

Sum == Add(a, b)

VARIABLES result, done

vars == <<result, done>>

TypeOK ==
    /\ result \in Nat
    /\ done \in BOOLEAN

Init ==
    /\ result = 0
    /\ done = FALSE

Compute ==
    /\ done = FALSE
    /\ result' = Sum
    /\ done' = TRUE

Terminated ==
    /\ done = TRUE
    /\ UNCHANGED vars

Next == Compute \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Compute)

CorrectResult == done => result = a + b

ResultStable == [][done => (result' = result /\ done' = done)]_vars

EventuallyComputed == <>(done /\ result = a + b)

THEOREM Spec => [](TypeOK /\ CorrectResult)
=============================================================================