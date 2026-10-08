```tla
------------------------------ MODULE Toggle ------------------------------
EXTENDS TLC

VARIABLE state

(* --- Initial condition ------------------------------------------------- *)
Init == state = TRUE

(* --- Transition relation ----------------------------------------------- *)
Next ==
  \/ state' = ~state   \* Flip the boolean value
  \/ state' = state    \* Stuttering step (no change)

(* --- Full temporal specification --------------------------------------- *)
Spec == Init /\ []Next

(* --- Safety property: the state is always a Boolean -------------------- *)
Prop == [] (state \in BOOLEAN)

(* --- Additional invariants for reasoning --------------------------------*)
StrongInvariant == [] (state = TRUE)          \* State stays true forever
WeakObservation  == <> (state = TRUE)         \* State becomes true infinitely often

(* --- Theorems that can be proved or checked by TLC --------------------- *)
THEOREM PropThm:            Spec => Prop
THEOREM StrongInvThm:       Spec => StrongInvariant
THEOREM WeakObsThm:        Spec => WeakObservation

END Toggle
```