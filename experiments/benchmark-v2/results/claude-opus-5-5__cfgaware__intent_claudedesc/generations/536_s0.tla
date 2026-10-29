---------------------------- MODULE MaxFinder ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Tuples, minValue

ASSUME minValue \in Int

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ I = 1..Len(inp)
    /\ pc = "Lbl"

Step ==
    /\ pc = "Lbl"
    /\ I # {}
    /\ \E i \in I :
          /\ max' = IF inp[i] > max THEN inp[i] ELSE max
          /\ I' = I \ {i}
    /\ pc' = "Lbl"
    /\ UNCHANGED inp

Finish ==
    /\ pc = "Lbl"
    /\ I = {}
    /\ pc' = "Done"
    /\ UNCHANGED << inp, max, I >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

Termination == <>(pc = "Done")

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ I \subseteq 1..Len(inp)
    /\ pc \in {"Lbl", "Done"}

Correctness ==
    pc = "Done" =>
        IF inp = << >>
            THEN max = minValue
            ELSE /\ \E j \in 1..Len(inp) : max = inp[j]
                 /\ \A j \in 1..Len(inp) : max >= inp[j]

=============================================================================