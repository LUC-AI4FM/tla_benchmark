---------------------------- MODULE RecursiveClock ----------------------------
EXTENDS Naturals

VARIABLE clock

vars == <<clock>>

(***************************************************************************)
(* Two recursive operators.                                                *)
(*   Check(n) recurses down to 0 and always yields TRUE.                   *)
(*   Flip(b, n) negates the Boolean b exactly n times.                     *)
(***************************************************************************)
RECURSIVE Check(_)
Check(n) == IF n = 0 THEN TRUE ELSE Check(n - 1)

RECURSIVE Flip(_, _)
Flip(b, n) == IF n = 0 THEN b ELSE Flip(~b, n - 1)

(***************************************************************************)
(* Type predicate.                                                         *)
(***************************************************************************)
TypeOK == clock \in BOOLEAN

(***************************************************************************)
(* Initial-state predicate.  It calls the recursive operator Check.        *)
(* TLC's coverage reporting counts this recursive call in Init: the        *)
(* sub-expressions of Check are evaluated once per recursion level during  *)
(* initial-state generation, so coverage shows several evaluations of      *)
(* Check's body even though only two initial states are generated.         *)
(***************************************************************************)
Init == /\ clock \in BOOLEAN
        /\ Check(3)

(***************************************************************************)
(* The transition flips the Boolean value of clock.                        *)
(***************************************************************************)
Next == clock' = Flip(clock, 1)

(***************************************************************************)
(* A separate, constraint-like state predicate that also uses the          *)
(* recursive operators.                                                    *)
(***************************************************************************)
Constraint == /\ Check(2)
              /\ Flip(clock, 2) = clock

Spec == Init /\ [][Next]_vars

=============================================================================