------------------------------ MODULE SimpleCheck ------------------------------
VARIABLES x, done

(* Initial state: x in 1..10 and not yet checked *)
Init == /\ x \in 1..10
        /\ done = FALSE

(* One observable action that asserts x^2 <= 100 and marks termination *)
CheckAction ==
    /\ ~done
    /\ x * x <= 100
    /\ done' = TRUE
    /\ UNCHANGED <<x>>

(* After termination, only stuttering transitions are allowed *)
Stutter == 
    /\ done
    /\ UNCHANGED <<x, done>>

Next == CheckAction \/ Stutter

Spec == Init /\ [][Next]_{<<x, done>>} /\ WF_acts(CheckAction)

Safety == [] (x * x <= 100)
Termination == <> done
===============================================================================