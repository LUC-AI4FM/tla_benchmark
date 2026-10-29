------------------------- MODULE NondeterministicMax -------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Input,     \* the input sequence of integers
          MinValue   \* the sentinel minimum value

ASSUME InputAssumption ==
    /\ MinValue \in Int
    /\ Input \in Seq(Int)
    /\ \A i \in 1..Len(Input) : Input[i] > MinValue

VARIABLES unseen,  \* indices of Input not yet examined
          result,  \* maximum value found so far
          pc       \* control state: "Lbl" while processing, "Done" at the end

vars == <<unseen, result, pc>>

Indices == 1..Len(Input)

TypeOK ==
    /\ unseen \subseteq Indices
    /\ result \in Int
    /\ pc \in {"Lbl", "Done"}

Init ==
    /\ unseen = Indices
    /\ result = MinValue
    /\ pc = "Lbl"

\* Examine an arbitrary, not-yet-examined element (nondeterministic order).
Step ==
    /\ pc = "Lbl"
    /\ unseen # {}
    /\ \E i \in unseen :
         /\ result' = IF Input[i] > result THEN Input[i] ELSE result
         /\ unseen' = unseen \ {i}
    /\ UNCHANGED pc

\* All elements have been examined exactly once: terminate.
Finish ==
    /\ pc = "Lbl"
    /\ unseen = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<unseen, result>>

\* Allow stuttering after termination to avoid reporting deadlock.
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
\* Correctness properties

Range == {Input[i] : i \in Indices}

\* Validity: on termination with non-empty input, result is an element of the input.
Validity ==
    (pc = "Done" /\ Len(Input) > 0) => result \in Range

\* Maximality: on termination with non-empty input, result >= every element.
Maximality ==
    (pc = "Done" /\ Len(Input) > 0) => \A i \in Indices : result >= Input[i]

\* Default behavior: on termination with empty input, result is the sentinel.
DefaultBehavior ==
    (pc = "Done" /\ Len(Input) = 0) => result = MinValue

\* Inductive helper invariant: result is the max over the examined elements.
ProgressInv ==
    /\ \A i \in Indices \ unseen : result >= Input[i]
    /\ (Indices \ unseen = {}) => result = MinValue
    /\ (Indices \ unseen # {}) => \E i \in Indices \ unseen : result = Input[i]

Correctness == Validity /\ Maximality /\ DefaultBehavior

\* Termination: the algorithm always terminates.
Termination == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ ProgressInv /\ Correctness)
THEOREM Spec => Termination
=============================================================================