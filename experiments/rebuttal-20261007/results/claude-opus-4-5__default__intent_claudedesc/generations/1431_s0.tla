---------------------------- MODULE StateConstraintLivenessPitfall ----------------------------
(***************************************************************************)
(* This specification demonstrates a subtle pitfall when using state       *)
(* constraints together with liveness properties in TLA+.                  *)
(*                                                                         *)
(* The system cycles indefinitely between states A and B, with weak        *)
(* fairness ensuring progress. A state constraint bounds the history log   *)
(* to keep model checking tractable.                                       *)
(*                                                                         *)
(* THE PITFALL: We assert a liveness property claiming the system          *)
(* eventually reaches "Done". This property is FALSE in the real system    *)
(* (the system never reaches Done), but when a state constraint is active, *)
(* it may be SPURIOUSLY REPORTED AS SATISFIED.                             *)
(*                                                                         *)
(* Why? The state constraint cuts off all infinite behaviors before they   *)
(* can witness the property's violation. With no infinite counterexample   *)
(* behaviors surviving the constraint, TLC reports the liveness property   *)
(* as satisfied even though it's genuinely violated in the unconstrained   *)
(* system.                                                                 *)
(*                                                                         *)
(* WARNING: Never use state constraints when checking liveness properties! *)
(***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANTS
    MaxHistoryLength  \* Bound for the state constraint (e.g., set to 5)

VARIABLES
    state,    \* Current state: "A", "B", or "Done"
    history   \* Log of state transitions (sequence of states)

vars == <<state, history>>

TypeOK ==
    /\ state \in {"A", "B", "Done"}
    /\ history \in Seq({"A", "B", "Done"})

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ state = "A"
    /\ history = <<"A">>

-----------------------------------------------------------------------------
(* Actions *)

(* Transition from A to B *)
AtoB ==
    /\ state = "A"
    /\ state' = "B"
    /\ history' = Append(history, "B")

(* Transition from B to A *)
BtoA ==
    /\ state = "B"
    /\ state' = "A"
    /\ history' = Append(history, "A")

(* 
   Note: There is NO action that transitions to "Done"!
   The system cycles between A and B forever.
   This is intentional to demonstrate the pitfall.
*)

(* Combined next-state relation *)
Next ==
    \/ AtoB
    \/ BtoA

-----------------------------------------------------------------------------
(* State Constraint for Model Checking *)
(* 
   This constraint bounds the history length to make model checking tractable.
   
   DANGER: When this constraint is active during liveness checking, it 
   artificially truncates all behaviors, preventing the model checker from
   finding infinite counterexample behaviors that would violate liveness.
*)

StateConstraint ==
    Len(history) <= MaxHistoryLength

-----------------------------------------------------------------------------
(* Fairness Conditions *)

(* Weak fairness ensures the system always makes progress *)
Fairness ==
    /\ WF_vars(AtoB)
    /\ WF_vars(BtoA)

-----------------------------------------------------------------------------
(* Complete Specification *)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* The system is always in a valid state *)
SafetyInvariant ==
    state \in {"A", "B", "Done"}

(* The history accurately reflects the current state *)
HistoryConsistent ==
    Len(history) > 0 => history[Len(history)] = state

(* The system never reaches Done (this is actually TRUE and should pass) *)
NeverDone ==
    state /= "Done"

-----------------------------------------------------------------------------
(* Liveness Properties *)

(*
   SPURIOUS LIVENESS PROPERTY:
   
   This property claims the system eventually reaches "Done".
   
   TRUTH: This property is FALSE - the system NEVER reaches Done because
   there is no transition to the Done state. The system cycles A -> B -> A
   forever.
   
   WITH STATE CONSTRAINT: When StateConstraint is active, all behaviors
   are cut off at MaxHistoryLength. Since there are no infinite behaviors
   left to examine, TLC cannot find a counterexample and INCORRECTLY
   reports this property as SATISFIED.
   
   WITHOUT STATE CONSTRAINT: TLC would find the infinite cycle A -> B -> A
   -> B -> ... as a counterexample, correctly reporting the property as
   VIOLATED.
   
   This demonstrates why state constraints should NEVER be used when
   checking liveness properties!
*)

EventuallyDone ==
    <>(state = "Done")

(*
   This property is actually TRUE and should pass:
   The system always eventually returns to state A (due to fairness)
*)
AlwaysEventuallyA ==
    [](state = "A" \/ <>(state = "A"))

(*
   Another form: infinitely often in state A (TRUE property)
*)
InfinitelyOftenA ==
    []<>(state = "A")

(*
   And infinitely often in state B (also TRUE)
*)
InfinitelyOftenB ==
    []<>(state = "B")

=============================================================================