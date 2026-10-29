---------------------------- MODULE MaxNondet ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

minValue == -1

Tuples == UNION { [1..n -> 0..3] : n \in 0..3 }

ASSUME \A t \in Tuples : \A k \in 1..Len(t) : t[k] > minValue

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ I = 1..Len(inp)
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF I # {}
         THEN /\ \E i \in I :
                    /\ max' = IF inp[i] > max THEN inp[i] ELSE max
                    /\ I' = I \ {i}
              /\ pc' = "Lbl_1"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << max, I >>
    /\ UNCHANGED inp

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Lbl_1)

Termination == <>(pc = "Done")

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ I \subseteq 1..Len(inp)
    /\ pc \in {"Lbl_1", "Done"}

Correctness ==
    pc = "Done" =>
        IF inp # << >>
          THEN /\ \E k \in 1..Len(inp) : max = inp[k]
               /\ \A k \in 1..Len(inp) : max >= inp[k]
          ELSE max = minValue

PartialCorrectness ==
    /\ \A k \in (1..Len(inp)) \ I : max >= inp[k]
    /\ (max = minValue) \/ (\E k \in (1..Len(inp)) \ I : max = inp[k])
=============================================================================