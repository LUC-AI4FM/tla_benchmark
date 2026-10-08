---------------------------- MODULE OneVariableMachine ----------------------------
EXTENDS Integers

CONSTANT FixedConstant, BoundedRange, OutOfRangeValue
VARIABLE variable

TypeInvariant == variable \in 0..1
InitialCondition == variable = 0
NextStep ==
  /\ variable' = FixedConstant
  \/ variable' \in 0..BoundedRange
  \/ variable' = OutOfRangeValue
  \/ variable' = IF variable = 0 THEN 1 ELSE 0
  \/ variable' = IF variable = 1 THEN 0 ELSE 1
  \/ variable' = variable

Spec == InitialCondition /\ [][NextStep]_variable
THEOREM Spec => []TypeInvariant
=============================================================================