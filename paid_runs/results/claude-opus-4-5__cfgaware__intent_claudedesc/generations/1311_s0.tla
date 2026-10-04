---------------------------- MODULE GCD ----------------------------
EXTENDS Naturals

VARIABLES x, y, done

vars == <<x, y, done>>

Init ==
    /\ x = 24
    /\ y \in 1..50
    /\ done = FALSE

Swap ==
    /\ ~done
    /\ x /= 0
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ done' = done

Subtract ==
    /\ ~done
    /\ x /= 0
    /\ x >= y
    /\ x' = x - y
    /\ y' = y
    /\ done' = done

Terminate ==
    /\ ~done
    /\ x = 0
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y

Next ==
    \/ Swap
    \/ Subtract
    \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
    /\ done \in BOOLEAN

Termination == <>(done = TRUE)

=======================================================================