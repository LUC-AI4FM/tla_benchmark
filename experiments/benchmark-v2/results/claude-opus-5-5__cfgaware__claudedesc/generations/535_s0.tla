------------------------------- MODULE Session5 -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

ConstMinValue == -99999

ConstTuples == { <<1, 2, 3>> }

VARIABLES tuple, i, result, pc

vars == << tuple, i, result, pc >>

TypeOK ==
    /\ tuple \in Tuples
    /\ i \in Nat
    /\ result \in Int
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ tuple \in Tuples
    /\ i = 1
    /\ result = minValue
    /\ pc = "Loop"

Step ==
    /\ pc = "Loop"
    /\ i <= Len(tuple)
    /\ result' = IF tuple[i] > result THEN tuple[i] ELSE result
    /\ i' = i + 1
    /\ UNCHANGED << tuple, pc >>

Finish ==
    /\ pc = "Loop"
    /\ i > Len(tuple)
    /\ pc' = "Done"
    /\ UNCHANGED << tuple, i, result >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

Termination == <>(pc = "Done")

===============================================================================