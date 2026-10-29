---------------------------- MODULE FindMaxNondet ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME /\ minValue \in Int
       /\ \A t \in Tuples : \A n \in 1..Len(t) : t[n] \in Int /\ minValue < t[n]

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ I \subseteq 1..Len(inp)
    /\ pc \in {"lb1", "Done"}

Correct ==
    IF inp = << >>
      THEN max = minValue
      ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
           /\ \A n \in 1..Len(inp) : max >= inp[n]

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ I = 1..Len(inp)
    /\ pc = "lb1"

lb1 ==
    /\ pc = "lb1"
    /\ IF I # {}
         THEN /\ \E i \in I :
                   /\ max' = IF inp[i] > max THEN inp[i] ELSE max
                   /\ I' = I \ {i}
              /\ pc' = "lb1"
         ELSE /\ Assert(Correct, "Failure of assertion at line lb1.")
              /\ pc' = "Done"
              /\ UNCHANGED << max, I >>
    /\ UNCHANGED inp

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* Safety invariants
PartialCorrectness == (pc = "Done") => Correct

MaxInvariant ==
    /\ \A n \in (1..Len(inp)) \ I : max >= inp[n]
    /\ (max = minValue) \/ (\E n \in 1..Len(inp) : max = inp[n])

=============================================================================