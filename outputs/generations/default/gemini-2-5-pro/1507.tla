------------------------- MODULE RecursiveOperators -------------------------
EXTENDS Integers, TLC

CONSTANT Depth
ASSUME Depth \in Nat

VARIABLE clock

vars == <<clock>>

(***************************************************************************)
(* Recursive operators are defined to demonstrate their use in various     *)
(* predicates.                                                             *)
(***************************************************************************)
RECURSIVE Check(_,_)
Check(val, n) ==
    IF n = 0 THEN
        TRUE
    ELSE
        /\ val \in BOOLEAN
        /\ Check(val, n - 1)

RECURSIVE Flip(_,_)
Flip(val, n) ==
    IF n = 0 THEN
        val
    ELSE
        Flip(~val, n - 1)

(***************************************************************************)
(* Predicates defining the system's initial state and constraints.         *)
(***************************************************************************)

(*
 * This predicate uses a recursive operator to define a type constraint
 * on the state variable `clock`. It asserts that `clock` is a Boolean.
 * This is used as the main safety invariant for the specification.
 *)
TypePredicate == Check(clock, Depth)

(*
 * The initial state predicate. The value of `clock` is determined by
 * recursively flipping TRUE `Depth` times.
 *)
Init ==
    (*
     * When model checking this specification, TLC will report coverage for the
     * recursive call to `Flip` below. By running TLC with different values
     * for the CONSTANT `Depth` (e.g., Depth=0 and Depth=1), coverage for both
     * the `n=0` (base case) and `n>0` (recursive step) branches of the
     * operator will be observed.
     *)
    clock = Flip(TRUE, Depth)

(***************************************************************************)
(* The system's behavior, defined as a single next-state action.           *)
(***************************************************************************)
Tick == clock' = ~clock

Next == Tick

(***************************************************************************)
(* The complete specification and properties to be checked.                *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(*
 * The safety invariant to be checked by TLC. It asserts that the
 * `TypePredicate` holds in every reachable state.
 *)
Invariant == TypePredicate

=============================================================================