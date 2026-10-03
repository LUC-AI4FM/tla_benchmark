------------------------------ MODULE TinyClock ------------------------------
EXTENDS SETS

VARIABLE clock

(* Recursive operator that flips a Boolean value *)
Flip(b) == IF b THEN NOT Flip(FALSE) ELSE TRUE

(* Recursive operator that checks a Boolean value *)
Check(b) == IF b THEN NOT Check(FALSE) ELSE TRUE

(* Type predicate for the state variable *)
TypeOK == /\ clock \in BOOLEAN
          /\ Check(clock) = Flip(clock)

(* Constraint-like state predicate *)
Constraint == /\ Check(clock) = TRUE
             /\ Flip(clock) = NOT clock

(* Initial-state predicate *)
Init == /\ TypeOK
        /\ clock = FALSE
        /\ Check(clock) = TRUE   -- Note: recursive call in Init for TLC coverage

(* Next-state relation that flips the value of clock *)
Next == /\ TypeOK
        /\ clock' = Flip(clock)

===============================================================================