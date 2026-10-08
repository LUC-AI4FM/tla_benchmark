------------------------------- MODULE EuclidsGCD -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES x, y, done

Init == /\ x = 24
        /\ y \in 1..MaxValue
        /\ done = FALSE

Next ==
    \/ /\ ~done
       /\ x # 0
       /\ x < y
       /\ x' = y
       /\ y' = x - y
       /\ done' = FALSE
    \/ /\ ~done
       /\ x # 0
       /\ x >= y
       /\ x' = x - y
       /\ y' = y
       /\ done' = FALSE
    \/ /\ ~done
       /\ x = 0
       /\ x' = x
       /\ y' = y
       /\ done' = TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, done>>
    /\ WF_next(<<x, y, done>>)

=============================================================================