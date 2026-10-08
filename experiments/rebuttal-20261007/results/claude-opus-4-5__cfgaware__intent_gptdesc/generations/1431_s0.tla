---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences

CONSTANTS MaxHistoryLen

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
    /\ Len(history) < MaxHistoryLen
    /\ \/ /\ mode = "mode1"
          /\ mode' = "mode2"
          /\ history' = Append(history, "mode1")
       \/ /\ mode = "mode2"
          /\ mode' = "mode1"
          /\ history' = Append(history, "mode2")
    /\ done' = FALSE

StayInMode ==
    /\ done = FALSE
    /\ \/ /\ mode = "mode1"
          /\ mode' = "mode2"
       \/ /\ mode = "mode2"
          /\ mode' = "mode1"
    /\ history' = history
    /\ done' = FALSE

Terminate ==
    /\ done = FALSE
    /\ Len(history) >= 1
    /\ done' = TRUE
    /\ mode' = mode
    /\ history' = history

Next ==
    \/ SwitchMode
    \/ StayInMode
    \/ Terminate

Fairness == WF_vars(SwitchMode)

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInvariant == Len(history) <= MaxHistoryLen

LivenessProperty == <>(done = TRUE)

=============================================================================