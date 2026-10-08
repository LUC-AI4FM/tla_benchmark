---- MODULE OneBoolStateMachine ----
VARIABLES x

(* State predicates about the value of x *)
IsTrue == (x = TRUE)
IsFalse == (x = FALSE)

(* Initial condition: x starts as TRUE *)
Init == x = TRUE

(* Next-state relation: flip the boolean value of x *)
Next == x' = ~x

(* Stuttering step definition: no change to x *)
Stutter == x' = x

Spec == Init /\ [] (Next \/ Stutter)