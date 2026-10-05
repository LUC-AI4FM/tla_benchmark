---------------------------- MODULE CyclicController ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS HistoryBound

VARIABLES mode, history, done

vars == <<mode, history, done>>

TypeOK ==
    /\ mode \in {"mode1", "mode2"}
    /\ history \in Seq({"mode1", "mode2"})
    /\ done \in BOOLEAN

Init ==
    /\ mode = "mode1"
    /\ history = <<>>
    /\ done = FALSE

SwitchMode ==
    /\ done = FALSE
    /\ Len(history) < HistoryBound
    /\ \/ /\ mode = "mode1"
          /\ mode' = "mode2"
          /\ history' = Append(history, "mode1")
       \/ /\ mode = "mode2"
          /\ mode' = "mode1"
          /\ history' = Append(history, "mode2")
    /\ done' = FALSE

StayInMode ==
    /\ done = FALSE
    /\ \/ /\ mode = "mode2"
          /\ mode' = "mode1"
       \/ /\ mode = "mode1"
          /\ mode' = "mode2"
    /\ history' = history
    /\ done' = FALSE

GoToDone ==
    /\ done = FALSE
    /\ Len(history) >= 2
    /\ done' = TRUE
    /\ mode' = mode
    /\ history' = history

Stutter ==
    /\ done = TRUE
    /\ UNCHANGED vars

Next ==
    \/ SwitchMode
    \/ StayInMode
    \/ GoToDone
    \/ Stutter

Fairness ==
    /\ WF_vars(SwitchMode)
    /\ WF_vars(GoToDone)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

HistoryBoundInvariant == Len(history) <= HistoryBound

SafetyInvariant ==
    /\ TypeOK
    /\ HistoryBoundInvariant

EventuallyDone == <>done

LivenessProperty == EventuallyDone

=============================================================================