-------------------------------- MODULE Euclid --------------------------------
EXTENDS Integers

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, done

vars == <<x, y, done>>

Init ==
    /\ x = 24
    /\ y \in 1..N
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

Finish ==
    /\ ~done
    /\ x = 0
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next ==
    \/ Swap
    \/ Subtract
    \/ Finish
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ x \in Nat
    /\ y \in Nat
    /\ done \in BOOLEAN

PositiveY ==
    y >= 1

ResultWhenDone ==
    done => (x = 0 /\ y >= 1)

Termination ==
    <>(done = TRUE)

================================================================================