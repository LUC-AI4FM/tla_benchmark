MODULE PCR
EXTENDS Naturals, Integers, TLC

CONSTANTS
    INIT_P,
    INIT_D,
    INIT_S,
    INIT_H

VARIABLES
    T, P, D, S, H

Temp == {"Heating", "Cooling", "Annealing", "Extension"}

Init ==
    /\ T = "Cooling"
    /\ P = INIT_P
    /\ D = INIT_D
    /\ S = INIT_S
    /\ H = INIT_H

Heating ==
    /\ T' = "Heating"
    /\ P' = P
    /\ D' = D
    /\ S' = S
    /\ H' = H

Cooling ==
    /\ T' = "Cooling"
    /\ P' = P
    /\ D' = D
    /\ S' = S
    /\ H' = H

Annealing ==
    /\ T' = "Annealing"
    /\ \E k \in 0..MIN(P,S) :
        P' = P - k
        S' = S - k
        H' = H + k
        D' = D

Extension ==
    /\ T' = "Extension"
    /\ D' = D + H
    /\ H' = 0
    /\ P' = P
    /\ S' = S

Next == Heating \/ Cooling \/ Annealing \/ Extension

vars == <<T, P, D, S, H>>

NonNeg == /\ P >= 0 /\ D >= 0 /\ S >= 0 /\ H >= 0
TypeInvariant == T \in Temp
CountPreservation ==
    P + D + S + H = INIT_P + INIT_D + INIT_S + INIT_H

SafetyInvariants == NonNeg /\ TypeInvariant /\ CountPreservation

PrimersDepleted == P = 0
Liveness == ◇ PrimersDepleted

Spec == Init /\ [][Next]_vars

THEOREM Spec => SafetyInvariants
LTLSPEC Liveness