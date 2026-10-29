---------------------------- MODULE CoverageRecursive ----------------------------
(***************************************************************************)
(* A boolean clock that toggles between TRUE and FALSE on every step.     *)
(* It exists to exercise TLC's coverage reporting for recursive           *)
(* operators. The initial state, the state constraint and the type        *)
(* invariant are each defined through a recursive operator.               *)
(*                                                                         *)
(* Edge case: in Init, the recursive call InitVal(Depth) is used as the   *)
(* initializer of clock. TLC may leave this call out of its coverage      *)
(* report, even though it evaluates the call's parameters.                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Depth

ASSUME DepthIsNat == Depth \in Nat

VARIABLE clock

vars == << clock >>

-----------------------------------------------------------------------------
(* Recursive operator that computes the initial clock value.              *)
(* It recurses down to 0 and then returns FALSE.                          *)
RECURSIVE InitVal(_)
InitVal(n) ==
    IF n = 0 THEN FALSE
             ELSE InitVal(n - 1)

(* Recursive operator used as the state constraint.                       *)
(* It always holds, but it is evaluated through recursion.                *)
RECURSIVE ConstraintRec(_, _)
ConstraintRec(b, n) ==
    IF n = 0 THEN b \in BOOLEAN
             ELSE ConstraintRec(b, n - 1)

(* Recursive check that x is a boolean. It walks the elements of a set    *)
(* one at a time.                                                         *)
RECURSIVE IsIn(_, _)
IsIn(x, S) ==
    IF S = {} THEN FALSE
    ELSE LET e == CHOOSE y \in S : TRUE
         IN  (x = e) \/ IsIn(x, S \ {e})

IsBool(x) == IsIn(x, BOOLEAN)

-----------------------------------------------------------------------------
(* The initial state comes from a recursive call that acts as the         *)
(* initializer of clock.                                                  *)
Init == clock = InitVal(Depth)

Tick == clock' = ~clock

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* State constraint, implemented through a recursive operator.            *)
StateConstraint == ConstraintRec(clock, Depth)

(* Type invariant: clock is always a boolean, checked recursively.        *)
TypeOK == IsBool(clock)

(* Liveness: under weak fairness the clock keeps toggling.                *)
ClockAlternates == []<>(clock = TRUE) /\ []<>(clock = FALSE)

THEOREM Spec => []TypeOK
=============================================================================