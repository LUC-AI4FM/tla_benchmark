---------------------------- MODULE SumConstants ----------------------------
(***************************************************************************)
(* A very small value-level arithmetic specification.  It declares two     *)
(* constants, Foo1 and Foo2, and defines the operator Sum as their         *)
(* addition over the natural numbers.  There is no transition system:      *)
(* no state variables, actions, fairness conditions or proofs.  The        *)
(* Init / Next / Spec definitions below are trivial placeholders that      *)
(* constrain no state, included only to satisfy the required module form. *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Foo1, Foo2

ASSUME ConstantsAreNaturals == Foo1 \in Nat /\ Foo2 \in Nat

\* The derived expression established by this module.
Sum == Foo1 + Foo2

(***************************************************************************)
(* Trivial placeholders: the module declares no variables, so there is     *)
(* no state to initialize and no step that can change anything.           *)
(***************************************************************************)
Init == TRUE

Next == FALSE

Spec == Init /\ [][Next]_<<>>

(***************************************************************************)
(* Value-level sanity properties (constant formulas).                      *)
(***************************************************************************)
SumIsNatural == Sum \in Nat

SumIsCommutative == Sum = Foo2 + Foo1

SumBoundsOperands == Foo1 <= Sum /\ Foo2 <= Sum

=============================================================================