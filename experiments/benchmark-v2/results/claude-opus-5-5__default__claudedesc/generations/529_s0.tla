---------------------------- MODULE Session3 ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ASSUME /\ minValue \in Int
       /\ \A t \in Tuples : /\ DOMAIN t = 1..Cardinality(DOMAIN t)
                            /\ \A k \in DOMAIN t : t[k] \in Int /\ minValue < t[k]

VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ i \in 1..(Len(inp) + 1)
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ i = 1
    /\ pc = "Loop"

Step ==
    /\ pc = "Loop"
    /\ IF i <= Len(inp)
         THEN /\ max' = IF inp[i] > max THEN inp[i] ELSE max
              /\ i' = i + 1
              /\ pc' = "Loop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << max, i >>
    /\ UNCHANGED inp

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Loop invariant: max is the maximum of the elements examined so far
LoopInv ==
    /\ \A k \in 1..(i - 1) : max >= inp[k]
    /\ (i > 1) => \E k \in 1..(i - 1) : max = inp[k]
    /\ (i = 1) => max = minValue

\* Partial correctness: upon termination, max is the maximum of the tuple
Correctness ==
    pc = "Done" =>
        /\ \A k \in DOMAIN inp : max >= inp[k]
        /\ (DOMAIN inp # {}) => \E k \in DOMAIN inp : max = inp[k]
        /\ (DOMAIN inp = {}) => max = minValue

\* Liveness: the algorithm eventually terminates
Termination == <>(pc = "Done")

=============================================================================