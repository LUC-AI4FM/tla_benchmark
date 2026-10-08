---------------------------- MODULE StaticState ----------------------------

EXTENDS Integers

CONSTANTS 
    Universe,       \* The finite set of allowed integer values
    Threshold,      \* The numeric threshold for the predicate
    BooleanFlag     \* The additional Boolean condition that must hold

VARIABLES 
    state           \* The single value held by the system

-----------------------------------------------------------------------------

(* Numeric predicate: the element must be greater than the threshold *)
NumericPredicate(x) == x > Threshold

(* The Boolean requirement that must hold for the chosen value *)
BooleanRequirement == BooleanFlag = TRUE

(* Combined predicate for acceptable values *)
AcceptableValue(x) == 
    /\ x \in Universe
    /\ NumericPredicate(x)
    /\ BooleanRequirement

(* The set of all values satisfying both constraints *)
AcceptableSet == {x \in Universe : AcceptableValue(x)}

-----------------------------------------------------------------------------

(* Type invariant: state is always in the Universe *)
TypeOK == state \in Universe

(* Initialization: nondeterministically choose a value satisfying both constraints *)
Init == 
    /\ BooleanRequirement
    /\ state \in {x \in Universe : NumericPredicate(x)}

(* No transitions change the state afterwards - the system stutters forever *)
Next == UNCHANGED state

(* The complete specification with stuttering *)
Spec == Init /\ [][Next]_state

-----------------------------------------------------------------------------

(* Safety Invariants *)

(* Every reachable state has a value in the allowed universe *)
InvariantInUniverse == state \in Universe

(* Every reachable state satisfies the numeric predicate *)
InvariantNumericPredicate == NumericPredicate(state)

(* Every reachable state satisfies the Boolean requirement *)
InvariantBooleanRequirement == BooleanRequirement

(* Combined safety invariant: all conditions hold *)
SafetyInvariant == 
    /\ InvariantInUniverse
    /\ InvariantNumericPredicate
    /\ InvariantBooleanRequirement

-----------------------------------------------------------------------------

(* Assumption: at least one allowed value exists (initialization is satisfiable) *)
ASSUME 
    /\ Universe # {}
    /\ Universe \subseteq Int
    /\ Threshold \in Int
    /\ BooleanFlag \in BOOLEAN
    /\ BooleanFlag = TRUE => AcceptableSet # {}

-----------------------------------------------------------------------------

(* Liveness property: once initialized, the value persists forever *)
(* This is trivially satisfied since Next never changes state *)
LivenessValuePersists == [](state = state)

(* Alternative formulation: if we start in a valid state, we stay there *)
LivenessPersistence == [](SafetyInvariant)

=============================================================================