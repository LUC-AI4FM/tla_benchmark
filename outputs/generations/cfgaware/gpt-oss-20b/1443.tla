------------------------------ MODULE SmallSM ------------------------------
EXTENDS Naturals

VARIABLE x

(* Initial condition *)
Init == x = 0

(* Transition relation: advance modulo 3 *)
Next == x' = (x + 1) Mod 3

(* Helper predicates *)
IsOne == x = 1
Done   == x = 2
Wrap   == x' = 0 /\ x = 2

(* Temporal specification with stuttering *)
Spec == Init /\ [][Next \/ x' = x]_x

(* TLC coverage check: each named predicate should be counted once *)
CHECK := ASSERT (TLCGet("coverage", "IsOne") = 1) /\
         (TLCGet("coverage", "Done")   = 1) /\
         (TLCGet("coverage", "Wrap")   = 1)

============================================================