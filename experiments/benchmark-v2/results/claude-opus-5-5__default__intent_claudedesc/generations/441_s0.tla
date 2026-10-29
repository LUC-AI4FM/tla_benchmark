---------------------------- MODULE EnabledTest ----------------------------
(***************************************************************************)
(* A minimal two-variable state machine used as a test bed for exploring   *)
(* the semantics of the ENABLED operator.                                  *)
(*                                                                         *)
(*   - x toggles between 0 and 1 on every step.                            *)
(*   - y is initialized to 0 and never changes.                            *)
(*                                                                         *)
(* ENABLED A holds in a state s iff there exists some state t such that    *)
(* the step s -> t satisfies A. The next state t is any assignment of      *)
(* values to the variables. It need not be reachable under Next. So:       *)
(*                                                                         *)
(*   - An action that only constrains primed variables, such as            *)
(*     x' = 0 /\ y' = 1, is enabled in EVERY state, because a              *)
(*     satisfying successor always exists.                                 *)
(*   - Adding a precondition on unprimed variables, such as x = 1,         *)
(*     makes the action enabled exactly when that precondition holds in    *)
(*     the current state.                                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y

vars == << x, y >>

-----------------------------------------------------------------------------
(* Type correctness *)
TypeOK == /\ x \in {0, 1}
          /\ y \in {0, 1}

-----------------------------------------------------------------------------
(* System behavior *)

Init == /\ x = 0
        /\ y = 0

Toggle == /\ x' = 1 - x
          /\ y' = y

Next == Toggle

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Hypothetical actions. These are NOT part of Next. They exist only so    *)
(* that their enablement can be examined.                                  *)

(* Constrains only next-state values. It sets x' = 0 and y' = 1.           *)
(* This transition never occurs in the system, because y stays 0.          *)
PrimedOnly == /\ x' = 0
              /\ y' = 1

(* The same transition with a precondition on the current state added.     *)
WithPrecondition == /\ x = 1
                    /\ x' = 0
                    /\ y' = 1

(* Enablement predicates. These are state predicates. *)
EnabledPrimedOnly == ENABLED PrimedOnly

EnabledWithPrecondition == ENABLED WithPrecondition

-----------------------------------------------------------------------------
(* Safety properties (invariants) *)

(* An action that constrains only primed variables is always enabled.      *)
(* This holds even though Next never takes such a step.                    *)
PrimedOnlyAlwaysEnabled == EnabledPrimedOnly

(* Adding a precondition can only shrink the enablement condition.         *)
PreconditionStrengthens == EnabledWithPrecondition => EnabledPrimedOnly

(* With the precondition, enablement equals the precondition itself.       *)
PreconditionCharacterization == EnabledWithPrecondition <=> (x = 1)

(* The precondition actually changes the result. The two enablement        *)
(* conditions differ exactly when x = 0.                                   *)
DifferenceCharacterization ==
    (EnabledPrimedOnly /\ ~EnabledWithPrecondition) <=> (x = 0)

(* y remains constant. *)
YConstant == y = 0

(* The system's own next-state action is always enabled, so no deadlock.   *)
NextAlwaysEnabled == ENABLED Next

Invariants == /\ TypeOK
              /\ PrimedOnlyAlwaysEnabled
              /\ PreconditionStrengthens
              /\ PreconditionCharacterization
              /\ DifferenceCharacterization
              /\ YConstant
              /\ NextAlwaysEnabled

-----------------------------------------------------------------------------
(* Liveness properties. These depend on WF_vars(Next).                     *)

(* x keeps toggling forever. *)
XInfinitelyOne  == []<>(x = 1)
XInfinitelyZero == []<>(x = 0)

(* The precondition-guarded action becomes enabled infinitely often, and   *)
(* disabled infinitely often, as the system evolves.                       *)
WithPreconditionInfinitelyEnabled  == []<>EnabledWithPrecondition
WithPreconditionInfinitelyDisabled == []<>~EnabledWithPrecondition

(* The primed-only action stays enabled forever. *)
PrimedOnlyPermanentlyEnabled == []EnabledPrimedOnly

(* The hypothetical transition never actually occurs (y' = 1 is never      *)
(* taken), even though it is always enabled.                               *)
PrimedOnlyNeverTaken == [][~PrimedOnly]_vars

THEOREM Spec => []Invariants
THEOREM Spec => /\ XInfinitelyOne
                /\ XInfinitelyZero
                /\ WithPreconditionInfinitelyEnabled
                /\ WithPreconditionInfinitelyDisabled
                /\ PrimedOnlyPermanentlyEnabled
                /\ PrimedOnlyNeverTaken
=============================================================================