---------------------------- MODULE ConcurrentSquare ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat /\ NSet # {}

ConstNSet == 0..3

VARIABLES n, i, x, pc

vars == <<n, i, x, pc>>

Phases == {"square", "advance", "Done"}

Init ==
    /\ n \in NSet
    /\ i = 0
    /\ x = 0
    /\ pc = "square"

\* Task A: in the "square" phase x = i^2 holds; if i < n, it advances
\* the control index and hands off to the advancing phase.
AdvanceIndex ==
    /\ pc = "square"
    /\ i < n
    /\ i' = i + 1
    /\ pc' = "advance"
    /\ UNCHANGED <<n, x>>

\* Task B: in the "advance" phase x = (i-1)^2; it updates the shared
\* value to match the new index, so that x = i^2 again.
UpdateShared ==
    /\ pc = "advance"
    /\ x' = x + 2 * i - 1
    /\ pc' = "square"
    /\ UNCHANGED <<n, i>>

\* Task A: when the index reached n, finish.
Finish ==
    /\ pc = "square"
    /\ i = n
    /\ pc' = "Done"
    /\ UNCHANGED <<n, i, x>>

\* Stuttering in the finished state (avoid deadlock reports).
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == AdvanceIndex \/ UpdateShared \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(AdvanceIndex \/ UpdateShared \/ Finish)

-----------------------------------------------------------------------------

TypeOK ==
    /\ n \in NSet
    /\ i \in 0..n
    /\ x \in 0..(n * n)
    /\ pc \in Phases

SquarePhaseInv  == (pc = "square")  => (x = i * i)

AdvancePhaseInv == (pc = "advance") => (i > 0 /\ x = (i - 1) * (i - 1))

DonePhaseInv    == (pc = "Done")    => (i = n /\ x = n * n)

SquareCorrect == (pc = "Done") => (x = n * n)

ReachableStateInv ==
    /\ TypeOK
    /\ SquarePhaseInv
    /\ AdvancePhaseInv
    /\ DonePhaseInv
    /\ SquareCorrect

Termination == <>(pc = "Done")

=============================================================================