------------------------------- MODULE PrisonersAndSwitches -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, PRISONERS, COUNTER
ASSUME N > 1 /\ PRISONERS = {p \in 1..N} /\ COUNTER \in PRISONERS

VARIABLES switches, visitedCount, prisonersVisited

Init == 
    /\ switches = <<FALSE, FALSE>>
    /\ visitedCount = 0
    /\ prisonersVisited = {}

Next ==
    \/ \/ \E p \in PRISONERS \ {COUNTER} :
            \/ \/ switches' = <<~switches[1], switches[2]>>
               /\ visitedCount' = visitedCount + (IF ~switches[1] THEN 1 ELSE 0)
               /\ prisonersVisited' = prisonersVisited
            \/ \/ switches' = <<switches[1], ~switches[2]>>
               /\ visitedCount' = visitedCount + (IF ~switches[2] THEN 1 ELSE 0)
               /\ prisonersVisited' = prisonersVisited
       \/ \E p \in {COUNTER} :
            \/ \/ switches' = <<~switches[1], switches[2]>>
               /\ visitedCount' = visitedCount
               /\ prisonersVisited' = prisonersVisited \cup {p}
            \/ \/ switches' = <<switches[1], ~switches[2]>>
               /\ visitedCount' = visitedCount
               /\ prisonersVisited' = prisonersVisited \cup {p}

Spec ==
    /\ Init
    /\ [][Next]_<<switches, visitedCount, prisonersVisited>>
    /\ WF_<<switches, visitedCount, prisonersVisited>>[Prisoners]

Termination ==
    /\ visitedCount >= N - 1
    /\ COUNTER \in prisonersVisited

SafetyInvariant ==
    \/ ~Termination
    \/ (\A p \in PRISONERS : p \in prisonersVisited)

Liveness ==
    <>[](Termination)

Prisoners == {p \in PRISONERS}

=============================================================================