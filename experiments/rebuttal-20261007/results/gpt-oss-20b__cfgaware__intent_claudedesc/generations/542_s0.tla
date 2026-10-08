------------------------------ MODULE ConcurrentIncrement ------------------------------
EXTENDS Naturals

VARIABLES x, p1_done, p2_done

Init ==
    /\ x = 0
    /\ p1_done = FALSE
    /\ p2_done = FALSE

P1Step ==
    /\ ~p1_done
    /\ x'   = x + 1
    /\ p1_done' = TRUE
    /\ p2_done' = p2_done

P2Step ==
    /\ ~p2_done
    /\ x'   = x + 1
    /\ p2_done' = TRUE
    /\ p1_done' = p1_done

Next == P1Step \/ P2Step

Spec == Init /\ [][Next]_<<x, p1_done, p2_done>>

=============================================================================