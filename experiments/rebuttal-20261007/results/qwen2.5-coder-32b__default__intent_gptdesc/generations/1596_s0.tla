------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES 
    \* Shared state: announcements of intent to enter critical section
    announce,
    \* Shared state: process currently in the critical section
    in_critical_section,
    \* Per-process local state: retry flag
    retry

Init == 
    /\ announce = [p \in 1..N -> FALSE]
    /\ in_critical_section = << >>
    /\ retry = [p \in 1..N -> FALSE]

TryEnterCS ==
    /\ \E p \in 1..N : \neg retry[p] /\ \neg announce[p]
    /\ \/ \A q \in 1..N \ {p} : \neg announce[q]
       \/ /\ announce[p]' = TRUE
          /\ retry' = [retry EXCEPT ![p] = FALSE]

Wait ==
    /\ \E p \in 1..N : announce[p] /\ \neg in_critical_section \in {[p]}
    /\ \/ \A q \in 1..N \ {p} : \neg announce[q]
       \/ /\ retry' = [retry EXCEPT ![p] = TRUE]

EnterCS ==
    /\ \E p \in 1..N : announce[p] /\ \neg in_critical_section \in {[p]}
    /\ /\ announce[p]' = FALSE
       /\ in_critical_section' = <<p>>

LeaveCS ==
    /\ in_critical_section /= << >>
    /\ in_critical_section' = << >>

Next == 
    \/ TryEnterCS
    \/ Wait
    \/ EnterCS
    \/ LeaveCS

Spec == Init /\ [][Next]_<<announce, in_critical_section, retry>>

\* Safety: Mutual Exclusion
MutualExclusion ==
    \A t \in StateTrace : Cardinality({p \in 1..N : p \in t.in_critical_section}) <= 1

\* Liveness: Global Eventual Entry Fairness
GlobalEventualEntry ==
    WF_<<announce, in_critical_section, retry>> (TryEnterCS)

\* Weak Fairness for each process's entry attempt
WeakFairness ==
    /\ \A p \in 1..N : SF_<<announce, in_critical_section, retry>> (p \in {q \in 1..N : announce[q] /\ \neg in_critical_section \in {[q]}})

=============================================================================