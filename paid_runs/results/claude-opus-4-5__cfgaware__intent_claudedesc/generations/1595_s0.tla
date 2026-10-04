---------------------------- MODULE spec ----------------------------

EXTENDS Naturals

VARIABLES counter, done

vars == <<counter, done>>

Init ==
    /\ counter = 0
    /\ done = FALSE

Increment ==
    /\ ~done
    /\ counter < 10
    /\ counter' = counter + 1
    /\ done' = IF counter' = 10 THEN TRUE ELSE FALSE

Stutter ==
    /\ done
    /\ UNCHANGED vars

Next ==
    \/ Increment
    \/ Stutter

Fairness ==
    WF_vars(Increment)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Termination ==
    <>(done = TRUE /\ counter = 10)

CounterAt5 ==
    counter = 5

CounterAt9AboutToFinish ==
    counter = 9 /\ ~done

=================================================================