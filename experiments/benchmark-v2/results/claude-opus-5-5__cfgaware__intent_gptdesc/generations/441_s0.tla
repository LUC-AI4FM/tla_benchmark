---------------------------- MODULE ToggleEnabled ----------------------------
EXTENDS Integers

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Initial state: both components are zero.                                *)
(***************************************************************************)
Init == x = 0 /\ y = 0

(***************************************************************************)
(* Each step toggles x between 0 and 1 and leaves y unchanged.             *)
(***************************************************************************)
Next == /\ x' = 1 - x
        /\ y' = y

(***************************************************************************)
(* Safety specification: start in Init, every step is a Next step          *)
(* (or a stuttering step).                                                 *)
(***************************************************************************)
SafeSpec == Init /\ [][Next]_vars

(***************************************************************************)
(* Liveness specification: weak fairness forces Next steps to occur        *)
(* whenever Next stays continuously enabled.                               *)
(***************************************************************************)
LiveSpec == SafeSpec /\ WF_vars(Next)

(***************************************************************************)
(* Elementary transitions.                                                 *)
(***************************************************************************)
SetX0Y1 == Next /\ x' = 0 /\ y' = 1
SetX1Y0 == Next /\ x' = 1 /\ y' = 0
SetX0Y0 == Next /\ x' = 0 /\ y' = 0
SetX1Y1 == Next /\ x' = 1 /\ y' = 1

(***************************************************************************)
(* F: characterizes when the transition setting x to 0 and y to 1 is       *)
(* enabled. It is enabled exactly when x = 1 and y = 1, because Next       *)
(* toggles x and preserves y.                                              *)
(***************************************************************************)
F == /\ (ENABLED SetX0Y1) <=> (x = 1 /\ y = 1)
     /\ (ENABLED SetX1Y0) <=> (x = 0 /\ y = 0)
     /\ (ENABLED SetX0Y0) <=> (x = 1 /\ y = 0)
     /\ (ENABLED SetX1Y1) <=> (x = 0 /\ y = 1)

(***************************************************************************)
(* G: implication relating the enabledness of a specific combined          *)
(* assignment to the enabledness of the Next action.                       *)
(***************************************************************************)
G == /\ (ENABLED SetX0Y1) => ENABLED Next
     /\ (ENABLED SetX1Y0) => ENABLED Next
     /\ (ENABLED (x' = 1 - x /\ y' = y)) <=> ENABLED Next

(***************************************************************************)
(* Safety invariant: reachable states have y = 0 and x in {0, 1}.          *)
(***************************************************************************)
Inv == /\ x \in {0, 1}
       /\ y = 0

(***************************************************************************)
(* Liveness: x keeps changing; in particular, x = 1 eventually holds and   *)
(* both values recur infinitely often.                                     *)
(***************************************************************************)
Progress == /\ []<>(x = 0)
            /\ []<>(x = 1)

FairnessHolds == []<>(ENABLED <<Next>>_vars) => []<><<Next>>_vars

THEOREM SafeSpec => []Inv
THEOREM LiveSpec => Progress
THEOREM SafeSpec => [](F /\ G)
=============================================================================