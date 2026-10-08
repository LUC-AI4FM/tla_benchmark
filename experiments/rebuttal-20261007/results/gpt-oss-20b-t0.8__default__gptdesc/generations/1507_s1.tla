------------------------------ MODULE TinyClock ------------------------------
EXTENDS Naturals, TLC

VARIABLE clock

(***************************************************************************
 *  Type predicate:  clock is a Boolean value.
 ***************************************************************************)
TypeOK == clock \in BOOLEAN

(***************************************************************************
 *  Recursive operator Check.  It simply returns TRUE when its argument
 *  is TRUE and FALSE otherwise.  The recursion here is trivial but
 *  demonstrates a recursive definition.
 ***************************************************************************)
Check(b) ==
  IF b THEN
    (* recursive call example: *)
    Check(FALSE)
  ELSE
    FALSE

(***************************************************************************
 *  Recursive operator Flip.  It returns the logical negation of its
 *  argument, using recursion to illustrate the form.
 ***************************************************************************)
Flip(b) ==
  IF b THEN
    FALSE
  ELSE
    TRUE

(***************************************************************************
 *  Initial-state predicate:  clock must be a Boolean and satisfy Check.
 ***************************************************************************)
Init == TypeOK /\ Check(clock)

(***************************************************************************
 *  Constraint-like state predicate.  It requires that Flip(clock) satisfies
 *  Check.  This is intended as an additional invariant constraint.
 ***************************************************************************)
Constraint == Check(Flip(clock))

(***************************************************************************
 *  Next-state relation:  the only action flips the value of clock.
 ***************************************************************************)
Next ==
  /\ clock' = Flip(clock)

(***************************************************************************
 *  Specification:  initial state, next-step behavior, and safety
 *  invariants (TypeOK and Constraint).  No liveness properties or
 *  fairness conditions are specified in the description.
 ***************************************************************************)
Spec == Init /\ [][Next]_clock /\ TypeOK /\ Constraint

=============================================================================