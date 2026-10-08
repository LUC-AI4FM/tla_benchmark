------------------------------ MODULE Github649 ------------------------------
EXTENDS TLC

VARIABLES clock

(* Recursive operator that checks if a value is Boolean after n recursions *)
Check(c, n) == IF n = 0 THEN c ∈ BOOLEAN ELSE Check(c, n-1)

(* Recursive operator that asserts v equals the negation of b after n recursions *)
Flip(v, b, n) == IF n = 0 THEN v = ~b ELSE Flip(v, b, n-1)

Init          == Flip(clock, FALSE, 1)
Next          == /\ clock' = ~clock
TypeOK        == Check(clock, 1)
Constraint    == Flip(clock, ~clock, 2)

(* Optional full specification *)
Spec          == Init /\ [][Next]_<<clock>>

=============================================================================