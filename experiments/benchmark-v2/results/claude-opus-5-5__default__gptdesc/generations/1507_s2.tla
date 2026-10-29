---- MODULE RecursiveClock ----
EXTENDS Naturals

VARIABLE clock

vars == <<clock>>

-----------------------------------------------------------------------------
(* Recursive helper operators *)

RECURSIVE Check(_, _)
(* Check(b, n) holds iff b is a Boolean; the recursion descends on n. *)
Check(b, n) == IF n = 0
                 THEN b \in BOOLEAN
                 ELSE Check(b, n - 1)

RECURSIVE Flip(_, _)
(* Flip(b, n) negates b exactly n times. *)
Flip(b, n) == IF n = 0
                THEN b
                ELSE Flip(~b, n - 1)

-----------------------------------------------------------------------------
(* Type predicate *)
TypeOK == Check(clock, 3)

(* Initial-state predicate.
   Note: TLC reports coverage for the recursive call to Check that
   appears here in Init. Each recursive unfolding is evaluated during
   initial-state generation, so its coverage counts are attributed to
   the Init definition rather than to the body of Check itself. *)
Init == /\ clock \in BOOLEAN
        /\ Check(clock, 2)
        /\ clock = Flip(TRUE, 2)

(* Separate constraint-like state predicate *)
Constraint == /\ Check(clock, 1)
              /\ Flip(clock, 2) = clock

-----------------------------------------------------------------------------
(* Transition: flip the Boolean value of clock *)
Tick == clock' = Flip(clock, 1)

Next == Tick

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)
THEOREM Spec => []TypeOK
THEOREM Spec => []Constraint

====