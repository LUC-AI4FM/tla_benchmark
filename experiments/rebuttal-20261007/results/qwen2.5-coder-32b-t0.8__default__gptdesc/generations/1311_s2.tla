------------------------------ MODULE GCDBySubtraction ------------------------------

EXTENDS Naturals

CONSTANTS pcInit

VARIABLES u, v, pc

Init == /\ u = 24 
        /\ v \in (1..50) 
        /\ pc = pcInit

StepPcInit == /\ pc = pcInit
                /\ u > 0
                /\ pc' = "Subtract"

StepSubtract == /\ pc = "Subtract"
                  /\ IF u < v THEN \/ u' = u /\ v' = u
                                   /\ pc' = "Swap"
                                 ELSE \/ u' = u - v 
                                      /\ pc' = "Subtract"

StepSwap == /\ pc = "Swap"
              /\ u' = v
              /\ v' = u
              /\ pc' = "Subtract"

StepDone == /\ pc = "Subtract"
             /\ u = 0
             /\ pc' = "Done"

Next == StepPcInit \/ StepSubtract \/ StepSwap \/ StepDone

Spec == /\ Init 
        /\ [][Next]_<<u, v, pc>>
        /\ WF_<<u, v>>[StepPcInit]
        /\ WF_<<u, v>>[StepSubtract]
        /\ WF_<<u, v>>[StepSwap]

=============================================================================