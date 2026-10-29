---------------------------- MODULE EnabledInstanceTest ----------------------------
EXTENDS Naturals

VARIABLE u

vars == <<u>>

G(v, A) == ENABLED ( A
                     \/ UNCHANGED <<u, v>>
                     \/ (u' = v /\ v' = u) )

H == (u' = u) /\ G(u, u' = u + 1)

Init == u = 0

Next == H

Spec == Init /\ [][Next]_vars

=============================================================================