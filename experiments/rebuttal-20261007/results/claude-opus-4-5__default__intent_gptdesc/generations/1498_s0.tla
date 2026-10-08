---------------------------- MODULE TwoActionToggle ----------------------------
EXTENDS Booleans

VARIABLES state

--------------------------------------------------------------------------------
(* Type invariant: state is always a boolean *)
TypeInvariant == state \in BOOLEAN

--------------------------------------------------------------------------------
(* Initial condition: state starts as FALSE *)
Init == state = FALSE

--------------------------------------------------------------------------------
(* Two equivalent toggle actions that flip the boolean value *)

Toggle1 == state' = ~state

Toggle2 == state' = ~state

--------------------------------------------------------------------------------
(* Next state relation: nondeterministically choose either toggle action *)
Next == Toggle1 \/ Toggle2

--------------------------------------------------------------------------------
(* Fairness: both actions are weakly fair to prevent starvation *)
Fairness == WF_state(Toggle1) /\ WF_state(Toggle2)

--------------------------------------------------------------------------------
(* Complete specification with fairness *)
Spec == Init /\ [][Next]_state /\ Fairness

--------------------------------------------------------------------------------
(* SAFETY PROPERTIES *)

(* The state is always a boolean - no other values allowed *)
AlwaysBoolean == state \in BOOLEAN

(* Each transition flips the value - captured by showing state changes *)
(* This is implicit in Toggle1 and Toggle2 definitions, but we can verify *)
(* that if state was FALSE it becomes TRUE and vice versa *)
TransitionFlipsValue == [][state' = ~state]_state

--------------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)

(* The system never gets stuck - there is always a next action available *)
(* This is expressed as: it's always possible to take a step *)
NeverStuck == []ENABLED(Next)

(* The system does not converge to a fixed point - toggling continues *)
(* Expressed as: infinitely often the state changes *)
NoFixedPoint == []<>(state' # state)

(* Alternative: the system keeps toggling - we see both values infinitely often *)
AlternatesForever == []<>(state = TRUE) /\ []<>(state = FALSE)

(* Reachable states alternate between FALSE and TRUE *)
(* This means we eventually see TRUE and eventually see FALSE repeatedly *)
ReachableStatesAlternate == []<>(state = TRUE) /\ []<>(state = FALSE)

--------------------------------------------------------------------------------
(* CORRECTNESS PROPERTIES TO CHECK *)

(* Every reachable state is either FALSE or TRUE *)
OnlyBooleanValues == state \in BOOLEAN

(* The system does not stop at a fixed point *)
(* Under fairness, if we can toggle, we eventually will *)
EventuallyToggles == [](ENABLED(Next) => <>(state' # state))

--------------------------------------------------------------------------------
(* Combined safety invariant *)
SafetyInvariant == TypeInvariant /\ AlwaysBoolean

(* Combined liveness property *)
LivenessProperty == NeverStuck /\ AlternatesForever

================================================================================