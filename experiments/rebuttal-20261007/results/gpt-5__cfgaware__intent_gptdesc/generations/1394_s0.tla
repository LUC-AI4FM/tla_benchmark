---- MODULE ThreeCompSpec ----
EXTENDS Naturals, Integers

CONSTANTS
    Max,      \* natural-number bound for the incrementing component
    YVals,    \* finite set of allowed values for the "unchanged" component
    C,        \* externally supplied constant value
    CDomain   \* finite set containing possible values for C

ASSUME /\ Max \in Nat
       /\ Max >= 0
       /\ C \in CDomain
       /\ YVals # {}
       /\ CDomain # {}

VARIABLES x, y, z

vars == << x, y, z >>

Guard == x < Max
Terminated == x = Max

Init ==
    /\ x \in 0..Max
    /\ y \in YVals
    /\ z = C

Inc ==
    /\ Guard
    /\ x' = x + 1
    /\ y' = y
    /\ z' = z

UpdateY ==
    /\ ~Guard
    /\ x' = x
    /\ y' \in YVals
    /\ z' = z

Next == Inc \/ UpdateY

TypeInv ==
    /\ x \in 0..Max
    /\ y \in YVals
    /\ z \in CDomain
    /\ z = C

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Inc)
====