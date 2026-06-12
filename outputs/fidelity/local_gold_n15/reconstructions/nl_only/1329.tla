---- MODULE TLCModelWrapper ----
EXTENDS EWD840, TLC

CONSTANTS ConcreteConstant

VARIABLES x

Init == TRUE

Next == /\ TRUE

Spec == EWD840!Spec

Liveness == EWD840!Liveness
========================================