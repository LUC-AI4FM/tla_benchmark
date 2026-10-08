```tla
------------------------------ MODULE SimpleVector ------------------------------
EXTENDS Naturals, TLC

CONSTANTS
    Indices,          \* Finite set of five indices (e.g., 1..5)
    DistVal,          \* Distinguished index value
    FixedConst,       \* Integer constant to write into the vector
    ControlSet        \* Set of allowed control values (same size as Indices)

VARIABLES
    ctrl,             \* Current control value
    vec               \* Vector of integer counters indexed by Indices

(* --------------------------------------------------------------------------- *)
(* Initial state:  control is chosen from ControlSet and all counters are zero. *)
Init ==
    /\ ctrl \in ControlSet
    /\ vec = [i \in Indices |-> 0]

(* --------------------------------------------------------------------------- *)
(* Transition relation:  control never changes; if it equals DistVal, the
   corresponding vector entry is overwritten with FixedConst, otherwise the
   vector stays unchanged. *)
Next ==
    /\ ctrl' = ctrl
    /\ IF ctrl = DistVal THEN
           vec' = [vec EXCEPT ![DistVal] = FixedConst]
       ELSE
           vec' = vec

(* --------------------------------------------------------------------------- *)
(* Complete specification:  initial state followed by repeated application of
   the transition relation. *)
Spec == Init /\ [] Next

(* --------------------------------------------------------------------------- *)
(* Safety properties that must hold in every behavior. *)

CtrlInvariant ==
    [] (ctrl' = ctrl)

VecIntInvariant ==
    [] (\A i \in Indices : vec[i] \in Int)

UpdateCorrectness ==
    [] (ctrl = DistVal => vec'[DistVal] = FixedConst)

NoChangeWhenNotDist ==
    [] (ctrl # DistVal => vec' = vec)

(* --------------------------------------------------------------------------- *)
(* Theorems asserting that the specification implies each safety property. *)

THEOREM CtrlInvariantThm: Spec => CtrlInvariant
THEOREM VecIntInvariantThm: Spec => VecIntInvariant
THEOREM UpdateCorrectnessThm: Spec => UpdateCorrectness
THEOREM NoChangeWhenNotDistThm: Spec => NoChangeWhenNotDist

END MODULE
```