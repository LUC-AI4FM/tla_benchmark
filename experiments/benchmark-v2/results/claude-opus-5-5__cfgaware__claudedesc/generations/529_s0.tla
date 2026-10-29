---------------------------- MODULE Session3_MC ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

VARIABLES input, idx, curMax, pc

vars == << input, idx, curMax, pc >>

ConstMinValue == -99999

ConstTuples == [ {1, 2, 3} -> {-3, -2, -1} ]

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

TypeOK ==
    /\ input \in Tuples
    /\ idx \in 1..(Cardinality(DOMAIN input) + 1)
    /\ curMax \in Int
    /\ pc \in {"loop", "done"}

Init ==
    /\ input \in Tuples
    /\ idx = 1
    /\ curMax = minValue
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ idx <= Cardinality(DOMAIN input)
    /\ curMax' = IF input[idx] > curMax THEN input[idx] ELSE curMax
    /\ idx' = idx + 1
    /\ UNCHANGED << input, pc >>

Finish ==
    /\ pc = "loop"
    /\ idx > Cardinality(DOMAIN input)
    /\ pc' = "done"
    /\ UNCHANGED << input, idx, curMax >>

Terminating ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

Correctness ==
    pc = "done" =>
        /\ curMax \in { input[k] : k \in DOMAIN input }
        /\ \A k \in DOMAIN input : input[k] <= curMax

PartialCorrect ==
    \A k \in 1..(idx - 1) : input[k] <= curMax

EventuallyDone == <>(pc = "done")

=============================================================================