------------------------------- MODULE PrisonersAndSwitches ------------------------------

CONSTANTS N \* Number of prisoners, with N > 1

Prisoner == 1..N

p2 == 2
p3 == 3

VARIABLES switches, visitedCount, counterTally

vars == <<switches, visitedCount, counterTally>>

Init == /\ switches = [1..2 -> FALSE]
        /\ visitedCount = [Prisoner -> 0]
        /\ counterTally = 0

Next ==
    \E p \in Prisoner :
        LET isCounter == (p = 1)
            otherSwitch == IF switches[1] THEN 2 ELSE 1
        IN
        \/ /\ ~isCounter
           /\ \/ switches[otherSwitch]
              /\ \/ /\ visitedCount[p] = 0
                 /\ switches' = [switches EXCEPT ![otherSwitch] = FALSE]
                    /\ visitedCount' = [visitedCount EXCEPT ![p] = 1]
                    /\ counterTally' = counterTally + 1
              [] /\ visitedCount[p] > 0
                 /\ \/ switches' = [switches EXCEPT ![1] = ~switches[1]]
                    /\ visitedCount' = visitedCount
                    /\ counterTally' = counterTally
        [] /\ isCounter
           /\ \/ \E p2 \in Prisoner \ {1} : visitedCount[p2] > 0
              /\ switches' = [switches EXCEPT ![otherSwitch] = FALSE]
                 /\ visitedCount' = [visitedCount EXCEPT ![p2] = 0]
                 /\ counterTally' = counterTally - (N - 1)
              [] /\ \/ switches' = [switches EXCEPT ![1] = ~switches[1]]
                 /\ visitedCount' = visitedCount
                 /\ counterTally' = counterTally

Spec == Init /\ [][Next]_<<vars>>

TypeOK ==
    /\ switches \in [1..2 -> BOOLEAN]
    /\ visitedCount \in [Prisoner -> 0..1]
    /\ counterTally \in 0..(N - 1)

CountInvariant ==
    /\ counterTally = Sum({visitedCount[p] : p \in Prisoner \ {1}})
    /\ \/ counterTally < N - 1
       /\ \A p2, p3 \in Prisoner \ {1} : visitedCount[p2] = visitedCount[p3]

Safety ==
    /\ CountInvariant
    /\ (counterTally = N - 1) => (\A p \in Prisoner : visitedCount[p] > 0)

Liveness ==
    <>(counterTally = N - 1)

=============================================================================