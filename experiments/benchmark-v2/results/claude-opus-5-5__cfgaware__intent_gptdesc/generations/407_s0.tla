---- MODULE StateGen ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Values == {1, 2, 3}

Init == /\ x = 0
        /\ y = 0

Choose == /\ \E v \in Values : x' = v
          /\ y' = y

Stutter == UNCHANGED vars

Next == Choose \/ Stutter

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in Values \cup {0}
          /\ y = 0

Inv == TRUE

\* Coverage: each target value is reachable in some execution.
\* Expressed as properties whose violation (checked as invariants of the
\* form x # v) would witness reachability.
NotReached(v) == x # v

Coverage == \A v \in Values : <>(x = v)

====