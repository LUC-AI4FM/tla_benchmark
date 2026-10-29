---------------------------- MODULE ComponentEnv ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

----------------------------------------------------------------------------
(* Environment: a single global binary variable, initialized to 0 and       *)
(* flipped between 0 and 1 on every step.                                   *)
----------------------------------------------------------------------------

EnvInit == x = 0

EnvNext == x' = 1 - x

Spec == EnvInit /\ [][EnvNext]_x /\ WF_x(EnvNext)

TypeOK == x \in {0, 1}

----------------------------------------------------------------------------
(* Parameterized component with two inputs a and b. It exposes an initial  *)
(* condition, a safety predicate and a liveness predicate.                 *)
----------------------------------------------------------------------------

CompInit(a, b) == a = b /\ a \in {0, 1}

CompSafety(a, b) == a \in {0, 1} /\ b \in {0, 1} /\ a = b

CompLiveness(a, b) == []<>(a = 1) /\ []<>(b = 0)

----------------------------------------------------------------------------
(* Instantiation: the component receives the global variable as both of    *)
(* its inputs.                                                              *)
----------------------------------------------------------------------------

InstInit     == CompInit(x, x)
InstSafety   == CompSafety(x, x)
InstLiveness == CompLiveness(x, x)

(* A different global property whose negation is asserted: x never        *)
(* leaves the binary domain, i.e. x = 2 is never reached.                  *)
OtherGlobal == x = 2

----------------------------------------------------------------------------
(* Properties checked by the model checker.                                *)
----------------------------------------------------------------------------

(* The component's initial condition holds in the initial state. *)
InitProperty == InstInit

(* The component's safety predicate together with the negation of another *)
(* global property: one positive and one negative fact about the instance. *)
Invariant == InstSafety /\ ~OtherGlobal

(* The component's liveness predicate under the environment's behavior. *)
LivenessProperty == InstLiveness

SafetyProperty == []InstSafety

----------------------------------------------------------------------------

THEOREM InitThm      == Spec => InitProperty
THEOREM SafetyThm    == Spec => []Invariant
THEOREM LivenessThm  == Spec => LivenessProperty
THEOREM TypeThm      == Spec => []TypeOK

=============================================================================