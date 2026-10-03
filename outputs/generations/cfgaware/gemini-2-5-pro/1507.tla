---- MODULE TinyRecursive ----
EXTENDS TLC, Naturals

VARIABLES clock

RECURSIVE Check(_)
Check(n) == IF n = 0 THEN TRUE ELSE Check(n - 1)

RECURSIVE Flip(_)
Flip(b) == ~b

TypeOK == clock \in BOOLEAN

(*
 TLC will evaluate Check(3) during parsing/initialization because it is a
 constant-level expression. The result (TRUE) is cached. This means the
 recursive calls do not add to the state space exploration time.
*)
Init ==
    /\ clock = TRUE
    /\ Check(3)

Constraint == Flip(clock) = ~clock

Next == clock' = ~clock

=============================================================================