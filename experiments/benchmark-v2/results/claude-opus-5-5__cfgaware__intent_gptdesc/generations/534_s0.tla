---------------------------- MODULE Max ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME /\ minValue \in Int
       /\ \A t \in Tuples : /\ t \in Seq(Int)
                            /\ \A i \in 1..Len(t) : minValue < t[i]

VARIABLES inp, max, I, done, pc

vars == <<inp, max, I, done, pc>>

PostCondition ==
    IF inp = << >>
      THEN max = minValue
      ELSE /\ \E i \in 1..Len(inp) : max = inp[i]
           /\ \A i \in 1..Len(inp) : max >= inp[i]

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ I = 1..Len(inp)
    /\ done = {}
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF I # {}
         THEN \E i \in I :
                /\ IF inp[i] > max
                     THEN max' = inp[i]
                     ELSE max' = max
                /\ I' = I \ {i}
                /\ done' = done \cup {i}
                /\ pc' = "Lbl_1"
         ELSE /\ Assert(PostCondition,
                        "Failure of postcondition: max is not the maximum")
              /\ pc' = "Done"
              /\ UNCHANGED <<max, I, done>>
    /\ UNCHANGED inp

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Lbl_1)

-----------------------------------------------------------------------------

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ I \subseteq 1..Len(inp)
    /\ done \subseteq 1..Len(inp)
    /\ pc \in {"Lbl_1", "Done"}

\* Every index is processed exactly once: processed and unprocessed
\* indices partition the domain of the input.
ExactlyOnce ==
    /\ I \cap done = {}
    /\ I \cup done = 1..Len(inp)

\* Candidate is always the maximum of the processed elements (or minValue).
CandidateInv ==
    IF done = {}
      THEN max = minValue
      ELSE /\ \E i \in done : max = inp[i]
           /\ \A i \in done : max >= inp[i]

Safety == (pc = "Done") => PostCondition

InputUnchanged == [][inp' = inp]_vars

Termination == <>(pc = "Done")

=============================================================================