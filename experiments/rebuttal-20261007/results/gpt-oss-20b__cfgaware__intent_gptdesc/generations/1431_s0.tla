------------------------------ MODULE TwoStateController ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS
    MAX_HISTORY,
    Mode1,
    Mode2

VARIABLES
    mode,
    history

(* --------------------------------------------------------------------------- *)
(* Type invariant:  the variables always have the expected types and bounds.   *)
(* --------------------------------------------------------------------------- *)

TypeInv ==
    /\ mode ∈ {Mode1, Mode2, "Done"}
    /\ history ∈ Seq({Mode1, Mode2})
    /\ Len(history) <= MAX_HISTORY

(* --------------------------------------------------------------------------- *)
(* Initial state:  start in Mode1 with an empty history.                       *)
(* --------------------------------------------------------------------------- *)

Init ==
    /\ mode = Mode1
    /\ history = <<>>

(* --------------------------------------------------------------------------- *)
(* Actions that describe the possible transitions.                            *)
(* --------------------------------------------------------------------------- *)

Switch ==
    /\ mode ∈ {Mode1, Mode2}
    /\ Len(history) < MAX_HISTORY
    /\ mode' = IF mode = Mode1 THEN Mode2 ELSE Mode1
    /\ history' = Append(history, mode)

Stay ==
    /\ mode ∈ {Mode1, Mode2}
    /\ mode' = mode
    /\ history' = history

Terminate ==
    /\ mode ∈ {Mode1, Mode2}
    /\ mode' = "Done"
    /\ history' = history

DoneStay ==
    /\ mode = "Done"
    /\ UNCHANGED <<mode, history>>

(* --------------------------------------------------------------------------- *)
(* Next-state relation:  either stay in the terminal state or perform one of   *)
(* the actions defined above.                                                 *)
(* --------------------------------------------------------------------------- *)

Next ==
    \/ (mode = "Done" /\ UNCHANGED <<mode, history>>)
    \/ (mode ∈ {Mode1, Mode2} /\ (Switch \/ Stay \/ Terminate))

vars == {mode, history}

Spec ==
    Init /\ [][Next]_vars

(* --------------------------------------------------------------------------- *)
(* Safety invariant:  the history never exceeds the configured bound.         *)
(* --------------------------------------------------------------------------- *)

SafetyInv == Len(history) <= MAX_HISTORY

(* --------------------------------------------------------------------------- *)
(* Liveness goal:  eventually reach the terminal state "Done".                *)
(* --------------------------------------------------------------------------- *)

LivenessGoal == <> (mode = "Done")

(* --------------------------------------------------------------------------- *)
(* Fairness constraint on the switching action to make the liveness goal     *)
(* meaningful.                                                                *)
(* --------------------------------------------------------------------------- *)

FairnessConstraint == WF_vars(Switch)

===============================================================================