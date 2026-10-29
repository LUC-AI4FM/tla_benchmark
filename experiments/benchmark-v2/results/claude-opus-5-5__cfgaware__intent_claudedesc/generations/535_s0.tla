---------------------------- MODULE MCTupleMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ConstMinValue == -1000

ConstTuples == { <<1, -2, 3>>, <<-5, 4, 0, 2>> }

ASSUME minValue \in Int
ASSUME \A t \in Tuples : t \in Seq(Int)

VARIABLES inp, i, max, pc

vars == << inp, i, max, pc >>

Init ==
    /\ inp \in Tuples
    /\ i = 1
    /\ max = minValue
    /\ pc = "Loop"

Loop ==
    /\ pc = "Loop"
    /\ IF i <= Len(inp)
         THEN /\ max' = IF inp[i] > max THEN inp[i] ELSE max
              /\ i' = i + 1
              /\ pc' = "Loop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << i, max >>
    /\ UNCHANGED inp

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ inp \in Tuples
    /\ i \in 1..(Len(inp) + 1)
    /\ max \in Int
    /\ pc \in {"Loop", "Done"}

Correctness ==
    pc = "Done" =>
        IF Len(inp) = 0
          THEN max = minValue
          ELSE /\ \E k \in 1..Len(inp) : max = inp[k]
               /\ \A k \in 1..Len(inp) : inp[k] <= max

Termination == <>(pc = "Done")

=============================================================================