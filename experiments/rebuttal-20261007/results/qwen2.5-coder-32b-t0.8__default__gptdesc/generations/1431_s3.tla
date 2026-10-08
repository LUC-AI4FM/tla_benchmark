----------------------------- MODULE TwoStateProcess -----------------------------

EXTENDS TLC, Sequences

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next ==
    \/ /\ pc = "A"
       /\ history \o <<pc>> = history'
       /\ pc' = "B"
    \/ /\ pc = "B"
       /\ history' = history
       /\ pc' = "A"

StateConstraint == Len(history) <= MaxHistoryLength

Spec ==
    /\ Init
    /\ [][Next]_<<pc, history>>
    /\ WF_[Next]_<<pc, history>>
    /\ []StateConstraint

(* The following liveness property is unreachable in the modeled behavior *)
EventuallyDone ==
    <>[](pc = "Done")

=============================================================================