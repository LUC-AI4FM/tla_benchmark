---------------------------- MODULE Max ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME /\ Tuples \subseteq Seq(Int)
       /\ minValue \in Int
       /\ \A t \in Tuples : \A n \in 1..Len(t) : minValue < t[n]

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Correct ==
    IF inp = << >>
        THEN max = minValue
        ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
             /\ \A n \in 1..Len(inp) : max >= inp[n]

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF I # {}
               THEN /\ \E i \in I :
                          /\ max' = IF inp[i] > max THEN inp[i] ELSE max
                          /\ I' = I \ {i}
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(Correct, "Failure of assertion at line 1, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << max, I >>
         /\ inp' = inp

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"Lbl_1", "Done"}

PartialCorrectness == (pc = "Done") => Correct

Termination == <>(pc = "Done")

=============================================================================