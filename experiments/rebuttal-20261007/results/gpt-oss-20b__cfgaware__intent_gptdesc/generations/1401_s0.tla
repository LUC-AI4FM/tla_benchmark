------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLE c

(* ------------------------------------------------------------------ *)
(* Initial state: the observable counter starts at 0.                  *)
Init == c = 0

(* ------------------------------------------------------------------ *)
(* Subcomponent increment action.  It is enabled only when the counter
   has not yet reached its bound (3).  The action increments the counter
   by exactly one.                                                     *)
Increment ==
  /\ c < 3
  /\ c' = c + 1

(* ------------------------------------------------------------------ *)
(* Main controller stutter step.  This step leaves the observable
   value unchanged and is allowed only when the subcomponent is not
   enabled (i.e., when c ≥ 3).                                            *)
Stutter ==
  /\ c >= 3
  /\ c' = c

(* ------------------------------------------------------------------ *)
(* The step relation of the system: either an increment or a stutter. *)
Step == Increment \/ Stutter

vars == {c}

(* ------------------------------------------------------------------ *)
(* Temporal specification: initial condition, persistent step
   relation, and weak fairness for the subcomponent's increment action. *)
Spec == Init /\ [][Step]_vars /\ WF_vars(Increment)

(* ------------------------------------------------------------------ *)
(* Liveness property: eventually the observable counter reaches 3.   *)
Prop == <> (c = 3)

============================================================