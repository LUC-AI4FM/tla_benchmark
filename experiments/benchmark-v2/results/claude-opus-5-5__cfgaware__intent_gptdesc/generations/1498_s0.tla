---------------------------- MODULE BooleanToggle ----------------------------
(***************************************************************************)
(* A simple two-action toggle system with a single boolean state.          *)
(* The state starts at FALSE.  At each step the system nondeterministically *)
(* performs one of two equivalent toggle actions, each of which flips the  *)
(* boolean value.  Time is unbounded, so toggling continues forever.        *)
(***************************************************************************)

VARIABLE b

vars == << b >>

-----------------------------------------------------------------------------
(* Type invariant: the state is always a boolean.                          *)
TypeOK == b \in BOOLEAN

(* Initial condition.                                                      *)
Init == b = FALSE

(* Two equivalent toggle actions.                                          *)
ToggleA == b' = ~b

ToggleB == b' = ~b

(* Next-state relation: either toggle action may be chosen at any step.    *)
Next == ToggleA \/ ToggleB

(* Fairness: both actions are weakly fair, so neither is starved and the   *)
(* system cannot stutter forever.                                          *)
Fairness == WF_vars(ToggleA) /\ WF_vars(ToggleB)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

(* Every reachable state is either FALSE or TRUE.                          *)
BooleanInvariant == b = FALSE \/ b = TRUE

(* Each transition actually flips the value.                               *)
FlipAction == [][Next => b' = ~b]_vars

(* Every non-stuttering step alternates the value.                         *)
Alternation == [][b' = ~b]_vars

(* The two-step behavior returns the value to where it started.            *)
TwoStepsReturn == [][(Next => (b' # b))]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)

(* The system never gets stuck: a next action is always available.         *)
NeverStuck == [](ENABLED Next)

(* No deadlock in the sense of the spec making progress forever.           *)
Progress == []<><<Next>>_vars

(* The system does not converge to a fixed point: both values recur       *)
(* infinitely often.                                                       *)
NoFixedPoint == ([]<>(b = TRUE)) /\ ([]<>(b = FALSE))

(* Value changes infinitely often.                                         *)
KeepsChanging == []<>(b' # b)_vars \/ []<><<b' # b>>_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []BooleanInvariant
THEOREM Spec => FlipAction
THEOREM Spec => Alternation
THEOREM Spec => NeverStuck
THEOREM Spec => NoFixedPoint
=============================================================================