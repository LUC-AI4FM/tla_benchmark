---------------------------- MODULE CounterSystem ----------------------------

EXTENDS Integers

VARIABLES outerX

-----------------------------------------------------------------------------
(* Inner module definition *)

Inner(x) ==
    LET 
        InnerStep == x < 3 /\ x' = x + 1
        InnerEnabled == x < 3
    IN
        [step |-> InnerStep, enabled |-> InnerEnabled]

-----------------------------------------------------------------------------
(* Outer module definitions *)

InnerInstance == Inner(outerX)

Init == outerX = 0

Next == 
    IF InnerInstance.enabled
    THEN outerX' = outerX + 1
    ELSE UNCHANGED outerX

Spec == Init /\ [][Next]_outerX /\ WF_outerX(InnerInstance.step)

-----------------------------------------------------------------------------
(* Safety invariant: outerX stays within bounds *)

TypeInvariant == outerX \in 0..3

Safety == outerX <= 3

-----------------------------------------------------------------------------
(* Liveness property: outerX eventually reaches 3 *)

Liveness == <>(outerX = 3)

=============================================================================