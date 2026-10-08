------------------------------- MODULE TwoStateController -------------------------------
EXTENDS Naturals, Sequences

CONSTANTS MaxHistoryLength

VARIABLES mode, history

Init == /\ mode \in {"mode1", "mode2", "done"}
        /\ history = << >>

Next ==
    \/ /\ mode = "mode1"
       /\ \/ \/ history' = Append(history, "mode1")
              /\ mode' = "mode2"
          \/ /\ history' = history
             /\ mode' \in {"mode1", "done"}
    \/ /\ mode = "mode2"
       /\ \/ \/ history' = Append(history, "mode2")
              /\ mode' = "mode1"
          \/ /\ history' = history
             /\ mode' \in {"mode2", "done"}
    \/ /\ mode \in {"mode1", "mode2"}
       /\ history' = history
       /\ mode' = "done"

Spec ==
    /\ Init
    /\ [][Next]_<<mode, history>>
    /\ WF_next(<<mode, history>>)

SafetyInvariant == Len(history) < MaxHistoryLength

LivenessProperty == <>[](mode = "done")

FairnessConstraint == WF_next(<<mode, history>>)

=============================================================================