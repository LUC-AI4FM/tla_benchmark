------------------------------ MODULE ToggleMachine ------------------------------
EXTENDS Integers

VARIABLES x, y

vars == <<x, y>>

-----------------------------------------------------------------------------
(* Initial state: both components equal zero.                                *)
-----------------------------------------------------------------------------
Init == /\ x = 0
        /\ y = 0

-----------------------------------------------------------------------------
(* The single step: toggle x between 0 and 1, leave y unchanged.             *)
(* Any step satisfying these constraints is allowed.                         *)
-----------------------------------------------------------------------------
Toggle == /\ x' = 1 - x
          /\ y' = y

Next == Toggle

-----------------------------------------------------------------------------
(* Specification. Weak fairness suffices because Toggle is enabled in every  *)
(* state, so it can never be only intermittently enabled.                    *)
-----------------------------------------------------------------------------
Safety == Init /\ [][Next]_vars

Fairness == WF_vars(Next)

Spec == Safety /\ Fairness

-----------------------------------------------------------------------------
(* Elementary transitions: a specific combined assignment of x and y.        *)
-----------------------------------------------------------------------------
Assign(a, b) == /\ x' = a
                /\ y' = b

(* The assignment (a, b) is enabled as a Next step from the current state.   *)
AssignEnabled(a, b) == ENABLED (Next /\ Assign(a, b))

(* The assignment x := 0, y := 1 is enabled exactly when x = 1 and y = 1.    *)
SetX0Y1Enabled == AssignEnabled(0, 1)

SetX0Y1EnabledCharacterization ==
    SetX0Y1Enabled <=> (x = 1 /\ y = 1)

(* General characterization of which elementary transitions are enabled.     *)
EnabledCharacterization ==
    \A a, b \in {0, 1} :
        AssignEnabled(a, b) <=> (a = 1 - x /\ b = y)

(* In every reachable state, the transition to x = 0 and y = 1 is disabled.  *)
SetX0Y1NeverEnabled == ~SetX0Y1Enabled

-----------------------------------------------------------------------------
(* Safety invariants.                                                        *)
-----------------------------------------------------------------------------
TypeOK == /\ x \in {0, 1}
          /\ y \in {0, 1}

(* The relationship imposed by the update rule and the initial condition:    *)
(* y is preserved at its initial value 0, and x is always 0 or 1.            *)
Inv == /\ y = 0
       /\ x \in {0, 1}

(* The Next action is always enabled, so there is no deadlock.               *)
AlwaysEnabled == ENABLED Next

-----------------------------------------------------------------------------
(* Refinement: if a specific combined assignment is enabled, then some       *)
(* action of the model is enabled.                                           *)
-----------------------------------------------------------------------------
AssignImpliesEnabled ==
    \A a, b \in {0, 1} : AssignEnabled(a, b) => ENABLED Next

ExistsEnabledAssign ==
    (ENABLED Next) <=> (\E a, b \in {0, 1} : AssignEnabled(a, b))

-----------------------------------------------------------------------------
(* Liveness properties.                                                      *)
-----------------------------------------------------------------------------
(* If Next is continuously enabled, then a Next step eventually occurs.      *)
Progress == <>[](ENABLED <<Next>>_vars) => []<><<Next>>_vars

(* x toggles forever.                                                        *)
InfinitelyOftenX0 == []<>(x = 0)
InfinitelyOftenX1 == []<>(x = 1)

(* Every state with x = 0 eventually leads to a state with x = 1, and back.  *)
LeadsToOne  == (x = 0) ~> (x = 1)
LeadsToZero == (x = 1) ~> (x = 0)

Liveness == /\ Progress
            /\ InfinitelyOftenX0
            /\ InfinitelyOftenX1
            /\ LeadsToOne
            /\ LeadsToZero

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []AlwaysEnabled
THEOREM Spec => []SetX0Y1EnabledCharacterization
THEOREM Spec => []EnabledCharacterization
THEOREM Spec => []SetX0Y1NeverEnabled
THEOREM Spec => []AssignImpliesEnabled
THEOREM Spec => []ExistsEnabledAssign
THEOREM Spec => Liveness
=============================================================================