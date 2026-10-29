---------------------------- MODULE MC ----------------------------
EXTENDS SingleLaneBridge, TLC

\* CONSTANT definitions @modelParameterConstants:0CarsRight
const_CarsRight ==
    {"r1", "r2"}

\* CONSTANT definitions @modelParameterConstants:1CarsLeft
const_CarsLeft ==
    {"l1", "l2"}

\* CONSTANT definitions @modelParameterConstants:2Bridge
const_Bridge ==
    {4, 5, 6}

\* CONSTANT definitions @modelParameterConstants:3Positions
const_Positions ==
    1..9

=============================================================================