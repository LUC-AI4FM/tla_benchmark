---- MODULE ToggleComponent ----
EXTENDS Naturals

VARIABLE v

vars == <<v>>

(***************************************************************************)
(* Environment: a single global binary variable, initialized to 0 and      *)
(* flipped between 0 and 1 on every step.                                  *)
(***************************************************************************)
EnvInit == v = 0

EnvNext == v' = 1 - v

Spec == EnvInit /\ [][EnvNext]_v /\ WF_v(EnvNext)

TypeOK == v \in {0, 1}

(***************************************************************************)
(* Parameterized component with two inputs a and b. It exposes three       *)
(* properties: an initial condition, a safety predicate over states and    *)
(* traces, and a liveness predicate.                                       *)
(***************************************************************************)
CompInit(a, b) == /\ a = b
                  /\ a \in {0, 1}

CompStateInv(a, b) == /\ a = b
                      /\ a \in {0, 1}
                      /\ b \in {0, 1}

CompSafety(a, b) == /\ [](CompStateInv(a, b))
                    /\ [][a' = b']_<<a, b>>

CompLiveness(a, b) == /\ []<>(a = 1)
                      /\ []<>(b = 0)

(***************************************************************************)
(* The component instantiated with the global variable v for both inputs.  *)
(***************************************************************************)
InstInit      == CompInit(v, v)
InstInv       == CompStateInv(v, v)
InstSafety    == CompSafety(v, v)
InstLiveness  == CompLiveness(v, v)

(***************************************************************************)
(* Some other global property, whose negation is also asserted: the        *)
(* environment eventually stabilizes at 0 forever. Since v keeps flipping  *)
(* under weak fairness, this property is false, so its negation holds.     *)
(***************************************************************************)
GlobalProp == <>[](v = 0)

PosAndNegProp == InstSafety /\ ~GlobalProp

(***************************************************************************)
(* Assertions about the instance in the context of the environment.        *)
(***************************************************************************)
THEOREM InitHolds      == Spec => InstInit
THEOREM TypeHolds      == Spec => []TypeOK
THEOREM InvHolds       == Spec => []InstInv
THEOREM SafetyHolds    == Spec => InstSafety
THEOREM LivenessHolds  == Spec => InstLiveness
THEOREM PosAndNegHolds == Spec => PosAndNegProp

====