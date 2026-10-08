------------------------------- MODULE PrisonersSwitchPuzzle -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prs, CounterPrisoner
VARIABLES switches, visitedCount

Init == /\ switches \in [1..2 -> {up, down}]
        /\ visitedCount = 0

Next ==
    LET nonCounterPrisoners == Prs \ {CounterPrisoner}
        designatedSwitch == 1
        otherSwitch == 2
    IN \/ /\ CHOOSE p \in Prs: TRUE
           /\ \/ /\ p = CounterPrisoner
                  /\ (switches[designatedSwitch] = down)
                     => /\ switches' = [switches EXCEPT ![designatedSwitch] = up]
                        /\ visitedCount' = visitedCount + 1
                  [] /\ switches' = switches
                     /\ visitedCount' = visitedCount
           [] /\ p \in nonCounterPrisoners
              /\ (visitedCount < Cardinality(Prs) - 1)
                 => /\ \/ /\ switches[designatedSwitch] = up
                        /\ switches' = [switches EXCEPT ![designatedSwitch] = down]
                   [] /\ switches' = [switches EXCEPT ![otherSwitch] = IF switches[otherSwitch] = up THEN down ELSE up]
              [] /\ p \in nonCounterPrisoners
                 /\ (visitedCount >= Cardinality(Prs) - 1)
                    => /\ switches' = switches
                       /\ visitedCount' = visitedCount

Spec ==
    /\ Init
    /\ [][Next]_<<switches, visitedCount>>
    /\ WF_<<switches, visitedCount>>(Next)

Safety == [](visitedCount >= Cardinality(Prs) - 1) => <>(/\ switches[1] = up /\ \/ CHOOSE p \in Prs: TRUE = CounterPrisoner)

Liveness == <>(visitedCount = Cardinality(Prs) - 1)

THEOREM Spec => []Safety
THEOREM Spec => <>Liveness

=============================================================================