---------------------------- MODULE FindMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A i \in 1..Len(t) : minValue < t[i]

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF I # {}
           THEN /\ \E i \in I :
                     /\ max' = IF inp[i] > max THEN inp[i] ELSE max
                     /\ I' = I \ {i}
                /\ pc' = "a"
           ELSE /\ Assert(IF inp = << >>
                            THEN max = minValue
                            ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                 /\ \A n \in 1..Len(inp) : max >= inp[n],
                          "Failure of assertion at line 1, column 1.")
                /\ pc' = "Done"
                /\ UNCHANGED << max, I >>
     /\ UNCHANGED inp

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================