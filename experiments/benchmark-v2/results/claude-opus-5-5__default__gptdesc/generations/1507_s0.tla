---------------------------- MODULE RecursiveClock ----------------------------
EXTENDS Naturals

VARIABLES clock

vars == << clock >>

-----------------------------------------------------------------------------
(* Recursive helper operators *)

RECURSIVE Check(_, _)
\* Check(b, n) evaluates the Boolean b after n recursive unfoldings.
Check(b, n) == IF n = 0 THEN b ELSE Check(b, n - 1)

RECURSIVE Flip(_, _)
\* Flip(v, n) negates the Boolean v exactly n times.
Flip(v, n) == IF n = 0 THEN v ELSE ~Flip(v, n - 1)

-----------------------------------------------------------------------------
(* Type predicate *)

TypeOK == Check(clock \in BOOLEAN, 3)

(* Initial-state predicate.                                                 *)
(* Note: TLC's coverage reporting attributes the evaluation of the          *)
(* recursive call to Flip below to each recursive unfolding; the call that  *)
(* appears in Init is evaluated only while generating initial states, so it *)
(* is reported once per initial state rather than per distinct state.       *)
Init == clock = Flip(FALSE, 2)

(* A separate constraint-like state predicate *)
Constraint == Check(Flip(clock, 2) \in BOOLEAN, 2)

-----------------------------------------------------------------------------
(* Transition: flip the Boolean value of clock *)

Tick == clock' = Flip(clock, 1)

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Constraint

=============================================================================