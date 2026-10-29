---------------------------- MODULE RecursiveClock ----------------------------
EXTENDS Naturals, TLC

VARIABLE clock

vars == << clock >>

-----------------------------------------------------------------------------
(* Recursive operators *)

RECURSIVE Check(_)
(* Check(v) is TRUE for every Boolean v. For FALSE it recurses once on TRUE. *)
Check(v) == IF v = TRUE
              THEN TRUE
              ELSE IF v = FALSE
                     THEN Check(TRUE)
                     ELSE FALSE

RECURSIVE Flip(_)
(* Flip(v) returns the negation of v, defined recursively. *)
Flip(v) == IF v = TRUE
             THEN FALSE
             ELSE ~Flip(TRUE)

-----------------------------------------------------------------------------
(* Type predicate *)
TypeOK == /\ clock \in BOOLEAN
          /\ Check(clock)

(* Initial-state predicate.                                                 *)
(* Note: TLC's coverage reporting for the recursive call Check(clock)       *)
(* appearing in Init may not be attributed like ordinary (non-recursive)    *)
(* expressions; recursive operator applications in Init are evaluated       *)
(* during initial-state generation and their coverage counts can differ.    *)
Init == /\ clock \in BOOLEAN
        /\ Check(clock)

(* Separate constraint-like state predicate *)
Constraint == Check(clock) /\ Flip(Flip(clock)) = clock

-----------------------------------------------------------------------------
(* Transition: flip the Boolean value of clock *)
Tick == clock' = Flip(clock)

Next == Tick

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)
THEOREM Spec => []TypeOK

=============================================================================