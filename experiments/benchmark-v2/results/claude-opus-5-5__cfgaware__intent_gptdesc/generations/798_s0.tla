---------------------------- MODULE FindMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets

\* Bounds used only to make the set of possible inputs finite for model checking
MaxLen == 3
MaxVal == 3

\* Sentinel value for the "empty" candidate maximum (not a natural number)
Sentinel == -1

\* All finite, nonempty sequences of naturals within the bounds
InputSeqs == UNION { [1..n -> 0..MaxVal] : n \in 1..MaxLen }

VARIABLES f, i, max, pc

vars == << f, i, max, pc >>

-------------------------------------------------------------------------

Init ==
    /\ f \in InputSeqs
    /\ i = 1
    /\ max = Sentinel
    /\ pc = "Lbl"

\* Inspect element i: update the candidate if it is larger, then advance the index
Step ==
    /\ pc = "Lbl"
    /\ i <= Len(f)
    /\ max' = IF f[i] > max THEN f[i] ELSE max
    /\ i' = i + 1
    /\ pc' = "Lbl"
    /\ UNCHANGED f

\* Index has passed the last element: the scan terminates
Finish ==
    /\ pc = "Lbl"
    /\ i > Len(f)
    /\ pc' = "Done"
    /\ UNCHANGED << f, i, max >>

\* Stuttering once terminated
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-------------------------------------------------------------------------
\* Type / domain invariant

TypeOK ==
    /\ f \in Seq(Nat)
    /\ Len(f) >= 1
    /\ i \in 1..(Len(f) + 1)
    /\ max \in Nat \cup {Sentinel}
    /\ pc \in {"Lbl", "Done"}

\* Inductive invariant: after inspecting the first i-1 elements,
\* the candidate dominates each of them (and is one of them if any were inspected)
InductiveInvariant ==
    /\ TypeOK
    /\ \A j \in 1..(i - 1) : max >= f[j]
    /\ (i > 1) => \E j \in 1..(i - 1) : max = f[j]
    /\ (i = 1) => max = Sentinel
    /\ (pc = "Done") => i = Len(f) + 1

\* Lemma: at termination, the index is exactly one past the last element
DoneIndexValue ==
    (pc = "Done") => (i = Len(f) + 1)

\* Postcondition: upon termination the candidate is a valid maximum
Correctness ==
    (pc = "Done") =>
        /\ \A j \in 1..Len(f) : max >= f[j]
        /\ \E j \in 1..Len(f) : max = f[j]

\* Liveness: the scan eventually finishes
Termination == <>(pc = "Done")

IndexReachesEnd == <>(i = Len(f) + 1)

-------------------------------------------------------------------------

THEOREM TypeCorrect == Spec => []TypeOK
THEOREM InvariantHolds == Spec => []InductiveInvariant
THEOREM DoneIndexLemma == Spec => []DoneIndexValue
THEOREM PostCondition == Spec => []Correctness
THEOREM Terminates == Spec => Termination

=============================================================================