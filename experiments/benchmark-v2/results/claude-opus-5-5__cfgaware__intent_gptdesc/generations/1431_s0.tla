---------------------------- MODULE CyclicController ----------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* A two-mode cyclic controller.  It starts in mode "A".  Each switching    *)
(* step moves to the other mode and records the mode it left in the        *)
(* history.  While in mode "B" the controller may also remain in "B"       *)
(* without appending to the history.  Once enough modes are recorded, the  *)
(* switch out of "B" leads to the terminal state "Done".                   *)
(***************************************************************************)

VARIABLES mode, history

vars == <<mode, history>>

Modes == {"A", "B"}
States == Modes \cup {"Done"}

\* Fixed small bound on the remembered history length.
HistBound == 4

\* Number of recorded entries after which leaving "B" terminates.
FinishThreshold == 3

TypeOK ==
    /\ mode \in States
    /\ history \in Seq(Modes)

Init ==
    /\ mode = "A"
    /\ history = << >>

\* Switch to the other mode, recording the previous mode in the history.
\* Once enough modes are recorded, leaving "B" reaches the terminal state.
Switch ==
    \/ /\ mode = "A"
       /\ mode' = "B"
       /\ history' = Append(history, "A")
    \/ /\ mode = "B"
       /\ Len(history) < FinishThreshold
       /\ mode' = "A"
       /\ history' = Append(history, "B")
    \/ /\ mode = "B"
       /\ Len(history) >= FinishThreshold
       /\ mode' = "Done"
       /\ UNCHANGED history

\* Remain in mode "B" without appending to the history.
Stay ==
    /\ mode = "B"
    /\ UNCHANGED vars

\* The terminal state stutters forever, so behaviors are infinite.
Terminated ==
    /\ mode = "Done"
    /\ UNCHANGED vars

Next == Switch \/ Stay \/ Terminated

\* Weak fairness: if Switch stays continuously enabled, it eventually occurs.
Fairness == WF_vars(Switch)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety / resource constraint: the history length stays below a fixed bound.
Constraint == Len(history) < HistBound

HistoryBounded == Len(history) < HistBound

\* Liveness goal: the system eventually reaches the terminal state.
Prop == <>(mode = "Done")

=============================================================================