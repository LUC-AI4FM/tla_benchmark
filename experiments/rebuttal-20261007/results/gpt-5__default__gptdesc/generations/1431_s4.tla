----------------------------- MODULE TwoStateHistory -----------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen

ASSUME MaxLen \in Nat

VARIABLES pc, history

vars == << pc, history >>

Init ==
    /\ pc = "A"
    /\ history = << >>

A ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ history' = Append(history, pc)

B ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ history' = history

Next == A \/ B

StateConstraint ==
    Len(history) <= MaxLen

TypeInv ==
    /\ pc \in {"A", "B"}
    /\ history \in Seq({"A"})

SafetyInv ==
    /\ TypeInv
    /\ StateConstraint

LivenessDone ==
    <> (pc = "Done")

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ [] StateConstraint

=============================================================================