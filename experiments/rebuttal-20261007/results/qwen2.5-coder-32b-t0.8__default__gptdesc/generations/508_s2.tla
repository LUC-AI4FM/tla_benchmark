------------------------------- MODULE SmallAlgorithm -------------------------------
EXTENDS Integers

CONSTANTS 
    \* No constants needed for this simple algorithm

VARIABLES 
    x, pc

Init == /\ x \in 1..10
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
              /\ x ^ 2 <= 100
              /\ pc' = "Done"
              /\ x' = x
          \/ /\ pc = "Done"
              /\ UNCHANGED <<x, pc>>

Spec == Init /\ [][Next]_<<x, pc>> /\ WF_next(<<x, pc>>)

(* Fairness conditions are not mentioned in the description *)

Termination == <><pc = "Done">_<<x, pc>>
=============================================================================