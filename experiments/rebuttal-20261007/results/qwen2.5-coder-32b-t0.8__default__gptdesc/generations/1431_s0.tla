---- MODULE TwoStateProcess ----

EXTENDS Naturals, Sequences

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next == \/ /\ pc = "A"
                 /\ history' = Append(history, "A")
                 /\ pc' = "B"
          \/ /\ pc = "B"
                 /\ history' = history
                 /\ pc' = "A"

Spec == /\ Init
        /\ [][Next]_<<pc, history>>
        /\ WF_(Next)_<<pc, history>>
        /\ \A h \in Seq("A") : Len(h) <= MaxHistoryLength => \/ pc = "Done"
                                                            \/ <>(pc = "Done")

====