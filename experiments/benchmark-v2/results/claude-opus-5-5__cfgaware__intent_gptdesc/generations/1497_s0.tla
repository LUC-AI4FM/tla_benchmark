---- MODULE ChooseMax ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

\* Fixed finite, totally ordered (by <) ranges used by the two transitions
R1 == 1..5
R2 == 3..8

InitVal == 0

\* Maximality predicate: m belongs to S and is strictly greater than every other element of S
IsMax(m, S) == /\ m \in S
               /\ \A k \in S \ {m} : m > k

\* Deterministic selection of an element meeting the maximality constraint
\* (only existence is required; CHOOSE picks it deterministically)
Max(S) == CHOOSE m \in S : IsMax(m, S)

\* Static preconditions on the ranges: finite, nonempty, and a maximum exists
RangeOK(S) == /\ S # {}
              /\ S \subseteq Nat
              /\ \E m \in S : IsMax(m, S)

Init == /\ x = InitVal
        /\ RangeOK(R1)
        /\ RangeOK(R2)

PickMax1 == /\ \E m \in R1 : IsMax(m, R1)
            /\ x' = Max(R1)

PickMax2 == /\ \E m \in R2 : IsMax(m, R2)
            /\ x' = Max(R2)

Next == PickMax1 \/ PickMax2

Spec == Init /\ [][Next]_vars /\ WF_vars(PickMax1) /\ WF_vars(PickMax2)

-----------------------------------------------------------------------------
\* Invariants

TypeOK == x \in Nat

\* (3) Safety: state is initial value or within the union of allowed ranges
StateInRanges == x = InitVal \/ x \in (R1 \cup R2)

\* Maximality holds for any chosen value
MaxHolds == x # InitVal => (IsMax(x, R1) \/ IsMax(x, R2))

Inv == TypeOK /\ StateInRanges /\ MaxHolds

\* (1) and (2): every chosen value lies in its range and is maximal
ChoiceCorrect ==
    /\ Max(R1) \in R1 /\ IsMax(Max(R1), R1)
    /\ Max(R2) \in R2 /\ IsMax(Max(R2), R2)

\* Action-level safety: every transition lands in the union of ranges with maximality
StepSafety ==
    [][ x' \in (R1 \cup R2) /\ (IsMax(x', R1) \/ IsMax(x', R2)) ]_vars

-----------------------------------------------------------------------------
\* (4) Liveness: continuously enabled transitions eventually produce their maxima

Live1 == <>(x = Max(R1))
Live2 == <>(x = Max(R2))
Liveness == Live1 /\ Live2

THEOREM Spec => []Inv
THEOREM Spec => []ChoiceCorrect
THEOREM Spec => StepSafety
THEOREM Spec => Liveness
=============================================================================