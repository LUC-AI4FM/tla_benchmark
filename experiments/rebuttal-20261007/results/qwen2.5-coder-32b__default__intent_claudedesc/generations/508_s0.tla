------------------------------- MODULE AssertCheck -------------------------------
EXTENDS Integers, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES 
    x,
    done

Init == /\ x \in 1..10
        /\ done = FALSE

Next == \/ /\ ~done
            /\ x' = x
            /\ done'
               <- (x * x) <= 100
         \/ /\ done
            /\ UNCHANGED <<x, done>>

Spec == Init /\ [][Next]_<<x, done>> /\ <>(done)

Termination == Spec => <>[](done)

=============================================================================