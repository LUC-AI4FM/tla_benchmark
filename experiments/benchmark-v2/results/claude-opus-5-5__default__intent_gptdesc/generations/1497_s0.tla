---------------------------- MODULE MaxChoice ----------------------------
(***************************************************************************)
(* A deterministic choice procedure that repeatedly selects the single     *)
(* maximum element of a fixed, finite, totally ordered range.  Two         *)
(* transitions, PickA and PickB, each choose the maximum of their own      *)
(* bounded range (0..N1 and 0..N2) and store it in the state variable x.   *)
(* The choice is specified only by existence of a value satisfying the     *)
(* maximality predicate, via CHOOSE.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N1,       \* upper bound of the range used by PickA
          N2,       \* upper bound of the range used by PickB
          InitVal   \* initial numeric state

ASSUME ConstAssump ==
    /\ N1 \in Nat
    /\ N2 \in Nat
    /\ InitVal \in Nat

R1 == 0..N1
R2 == 0..N2

(***************************************************************************)
(* Maximality: m is in S and strictly greater than every other element.   *)
(***************************************************************************)
IsMax(m, S) == /\ m \in S
               /\ \A y \in S \ {m} : m > y

(***************************************************************************)
(* Static preconditions on the ranges: finite, nonempty, and possessing   *)
(* an element meeting the maximality constraint.                           *)
(***************************************************************************)
ASSUME RangeAssump ==
    /\ IsFiniteSet(R1) /\ R1 # {}
    /\ IsFiniteSet(R2) /\ R2 # {}
    /\ \E m \in R1 : IsMax(m, R1)
    /\ \E m \in R2 : IsMax(m, R2)

(***************************************************************************)
(* Deterministic choice of the maximum; implementation unspecified.       *)
(***************************************************************************)
ChooseMax(S) == CHOOSE m \in S : IsMax(m, S)

VARIABLES x,      \* current numeric state
          last    \* which transition last executed: "none", "A" or "B"

vars == <<x, last>>

Init == /\ x = InitVal
        /\ last = "none"

PickA == /\ x' = ChooseMax(R1)
         /\ last' = "A"

PickB == /\ x' = ChooseMax(R2)
         /\ last' = "B"

Next == PickA \/ PickB

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(PickA)
        /\ WF_vars(PickB)

---------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ x \in Nat
          /\ last \in {"none", "A", "B"}

NatInv == x \in Nat

\* (1) Every chosen value is a member of its transition's range
ChosenInRange == /\ (last = "A") => x \in R1
                 /\ (last = "B") => x \in R2

\* (2) Every chosen value satisfies the maximality property
ChosenIsMax == /\ (last = "A") => IsMax(x, R1)
               /\ (last = "B") => IsMax(x, R2)

\* (3) Once a transition has occurred, the state is in the union of ranges
SafetyUnion == (last # "none") => x \in (R1 \cup R2)

\* Action-level safety: every transition lands in the union of ranges
StepSafety == [][Next => x' \in (R1 \cup R2)]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Liveness (4): a continuously enabled transition eventually executes    *)
(* and produces the maximum for its range.                                 *)
(***************************************************************************)
LiveA == []<>(last = "A" /\ IsMax(x, R1))
LiveB == []<>(last = "B" /\ IsMax(x, R2))

EnabledImpliesA == ([]ENABLED <<PickA>>_vars) => []<><<PickA>>_vars
EnabledImpliesB == ([]ENABLED <<PickB>>_vars) => []<><<PickB>>_vars

EventuallyChosen == <>(last # "none" /\ x \in (R1 \cup R2))

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ NatInv /\ ChosenInRange /\ ChosenIsMax /\ SafetyUnion)
THEOREM Spec => StepSafety
THEOREM Spec => EnabledImpliesA /\ EnabledImpliesB
=============================================================================