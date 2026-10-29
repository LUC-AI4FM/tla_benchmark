---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS minValue, Tuples

ConstMinValue == -1000

ConstTuples == [1..3 -> -3..-1]

ASSUME minValue \in Int

VARIABLES inp, i, max, pc

vars == <<inp, i, max, pc>>

N == 3

TypeOK ==
    /\ inp \in Tuples
    /\ i \in 1..(N + 1)
    /\ max \in Int
    /\ pc \in {"loop", "done"}

Init ==
    /\ inp \in Tuples
    /\ i = 1
    /\ max = minValue
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ i \in DOMAIN inp
    /\ max' = IF inp[i] > max THEN inp[i] ELSE max
    /\ i' = i + 1
    /\ UNCHANGED <<inp, pc>>

Finish ==
    /\ pc = "loop"
    /\ i \notin DOMAIN inp
    /\ pc' = "done"
    /\ UNCHANGED <<inp, i, max>>

Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

\* The computed value is the maximum of the tuple once the loop has completed.
Correct ==
    pc = "done" =>
        /\ \E k \in DOMAIN inp : max = inp[k]
        /\ \A k \in DOMAIN inp : inp[k] <= max

\* The running value never drops below the sentinel minimum.
AboveMin == max >= minValue

Termination == <>(pc = "done")
=============================================================================