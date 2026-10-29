---------------------------- MODULE MC ----------------------------
EXTENDS SingleLaneBridge, TLC

\* Model values representing the individual cars
CONSTANTS
    r1, r2

CONSTANTS
    l1, l2

\* Constant definition for CarsRight
const_CarsRight ==
    {r1, r2}

\* Constant definition for CarsLeft
const_CarsLeft ==
    {l1, l2}

\* Constant definition for Bridge
const_Bridge ==
    {4, 5}

\* Constant definition for Positions
const_Positions ==
    1..8

=============================================================================