---------------------------- MODULE TautologyDetector ----------------------------
(***************************************************************************)
(* A persistent tautology detector that maintains an immutable state       *)
(* and can always assert a boolean truth value. The system models a        *)
(* single immutable state component that never changes after initialization.*)
(***************************************************************************)

EXTENDS Booleans

CONSTANTS
    TruthValue      \* The fixed truth value the detector asserts

ASSUME TruthValueAssumption == TruthValue \in BOOLEAN

VARIABLES
    state           \* The immutable state component holding the truth value

vars == <<state>>

(***************************************************************************)
(* Type Invariant: The state is always a boolean value                     *)
(***************************************************************************)
TypeInvariant == state \in BOOLEAN

(***************************************************************************)
(* Initial Condition: The state is initialized to the fixed TruthValue    *)
(***************************************************************************)
Init == state = TruthValue

(***************************************************************************)
(* Transition Relation: No state change is permitted - the system stutters *)
(* This forbids any modification to the state component                    *)
(***************************************************************************)
Next == UNCHANGED state

(***************************************************************************)
(* The complete temporal specification with weak fairness                  *)
(* (fairness is vacuously satisfied since Next only stutters)             *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* The state always equals the initial TruthValue - immutability invariant
Immutability == state = TruthValue

\* The detector can always assert a boolean truth value
CanAssertTruth == state \in BOOLEAN

\* Combined safety invariant
SafetyInvariant == TypeInvariant /\ Immutability /\ CanAssertTruth

(***************************************************************************)
(* Temporal Properties                                                     *)
(***************************************************************************)

\* The system remains in the initial state for all time
AlwaysInInitialState == [](state = TruthValue)

\* The state never changes - expressed temporally
StateNeverChanges == [](state = TruthValue)

(***************************************************************************)
(* Abstract Boolean Proposition for Liveness Property                      *)
(* P(s) represents an arbitrary boolean proposition over the state         *)
(***************************************************************************)
Proposition(s) == s = TRUE

\* The proposition holds in current state
PropositionHolds == Proposition(state)

(***************************************************************************)
(* Reachability predicate: the proposition is reachable from current state *)
(* In this immutable system, reachable means it holds now                  *)
(***************************************************************************)
Reachable == PropositionHolds

(***************************************************************************)
(* Stability: once the proposition holds, it holds forever after           *)
(***************************************************************************)
StableProposition == [](PropositionHolds => []PropositionHolds)

(***************************************************************************)
(* Liveness-Derived Logical Property (THEOREM)                             *)
(*                                                                         *)
(* If at any time the system can reach a state where the proposition holds,*)
(* then there must exist a future point after which that proposition holds *)
(* permanently. Whenever the proposition becomes reachable, it becomes     *)
(* eventually stable forever after.                                        *)
(*                                                                         *)
(* Formally: <>(Reachable) => <>([]PropositionHolds)                       *)
(***************************************************************************)
LivenessProperty == <>(Reachable) => <>([]PropositionHolds)

\* Alternative formulation: if reachable now, eventually stable forever
ReachabilityImpliesEventualStability == Reachable => <>([]PropositionHolds)

\* Global temporal version: always, if reachable then eventually permanently true
GlobalLiveness == [](Reachable => <>([]PropositionHolds))

(***************************************************************************)
(* THEOREMS                                                                *)
(* These properties should be provable from Spec                           *)
(***************************************************************************)

THEOREM TypeCorrectness == Spec => []TypeInvariant

THEOREM ImmutabilityTheorem == Spec => []Immutability

THEOREM AlwaysCanAssert == Spec => []CanAssertTruth

THEOREM TemporalStability == Spec => AlwaysInInitialState

THEOREM StabilityTheorem == Spec => StableProposition

THEOREM MainLivenessTheorem == Spec => LivenessProperty

THEOREM GlobalLivenessTheorem == Spec => GlobalLiveness

=============================================================================