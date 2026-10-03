------------------------------- MODULE PlusCalExample -------------------------------
EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

(*--algorithm PlusCalExample
variables x = 0;

process ProcA = 
1: x := x + 1;
2: goto Done;

process ProcB =
1: x := x + 1;
2: goto Done;

end algorithm *)
\* Modification History
\* Last modified Mon Jan  1 00:00:00 UTC 2024 by Anonymous

CONSTANT <<ProcA, ProcB>>

VARIABLES pc

vars == <<x, pc>>

Proc ==
    case pc[ProcA] = 1 -> /\ x' = x + 1
                           /\ pc'[ProcA] = 2
                           /\ pc'[ProcB] = pc[ProcB]
    [] pc[ProcA] = 2 -> /\ x' = x
                          /\ pc'[ProcA] = 2
                          /\ pc'[ProcB] = pc[ProcB]
    [] pc[ProcB] = 1 -> /\ x' = x + 1
                           /\ pc'[ProcB] = 2
                           /\ pc'[ProcA] = pc[ProcA]
    [] pc[ProcB] = 2 -> /\ x' = x
                          /\ pc'[ProcB] = 2
                          /\ pc'[ProcA] = pc[ProcA]
    [] TRUE          -> /\ x' = x
                           /\ pc'[ProcA] = pc[ProcA]
                           /\ pc'[ProcB] = pc[ProcB]

Spec ==
    \E pc \in [<<ProcA, ProcB>> -> {1, 2}] :
        /\ pc[ProcA] = 1
        /\ pc[ProcB] = 1
        /\ x = 0
        /\ [][Proc]_<<x, pc>>

Terminating ==
    \/ pc[ProcA] = 2
    \/ pc[ProcB] = 2

Next == Proc \/ Terminating

Spec ==
    \E pc \in [<<ProcA, ProcB>> -> {1, 2}] :
        /\ pc[ProcA] = 1
        /\ pc[ProcB] = 1
        /\ x = 0
        /\ SpecFair(Next)

SpecFair == (Spec) /\ [](Terminating => <>[] Terminating)
=============================================================================