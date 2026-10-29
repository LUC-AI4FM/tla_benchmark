---------------------------- MODULE CyclicController ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS MaxHist          \* fixed small bound on the history length

ASSUME MaxHistAssumption == MaxHist \in Nat /\ MaxHist >= 2

Modes     == {"A", "B"}
Terminal  == "Done"
AllStates == Modes \cup {Terminal}

VARIABLES mode, history

vars == <<mode, history>>

Other(m) == IF m = "A" THEN "B" ELSE "A"

TypeOK ==
    /\ mode \in AllStates
    /\ history \in Seq(Modes)

Init ==
    /\ mode = "A"
    /\ history = << >>

\* Switch to the other mode, recording the previous mode in the history.
\* Only allowed while there is room left below the bound.
Switch ==
    /\ mode \in Modes
    /\ Len(history) < MaxHist - 1
    /\ mode' = Other(mode)
    /\ history' = Append(history, mode)

\* Remain in the other (second) mode without appending to the history.
Stay ==
    /\ mode = "B"
    /\ UNCHANGED vars

\* When the history has reached its capacity, the controller terminates.
Finish ==
    /\ mode \in Modes
    /\ Len(history) = MaxHist - 1
    /\ mode' = Terminal
    /\ UNCHANGED history

\* Terminal state: the system stays done forever (avoids deadlock).
Terminated ==
    /\ mode = Terminal
    /\ UNCHANGED vars

Next ==
    \/ Switch
    \/ Stay
    \/ Finish
    \/ Terminated

Fairness ==
    /\ WF_vars(Switch)
    /\ WF_vars(Finish)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: the remembered history always stays strictly below the bound.
HistoryBound == Len(history) < MaxHist

\* Safety: once done, the system remains done.
DoneIsStable == [][mode = Terminal => mode' = Terminal]_vars

\* Liveness: the system eventually reaches the terminal state.
EventuallyDone == <>(mode = Terminal)

\* Liveness (stronger): the system eventually stays done forever.
EventuallyAlwaysDone == <>[](mode = Terminal)

THEOREM Spec => [](TypeOK /\ HistoryBound)
THEOREM Spec => EventuallyDone
=============================================================================