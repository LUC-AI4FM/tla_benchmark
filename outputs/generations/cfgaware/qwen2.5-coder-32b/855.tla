---- MODULE PrisonersAndSwitches ----

CONSTANTS Prisoner

VARIABLES count, visited, switchA, switchB

p2 == CHOOSE pr \in Prisoner : pr # p1
p3 == CHOOSE pr \in Prisoner : pr # p1 /\ pr # p2

TypeOK ==
    /\ count \in 0..(Cardinality(Prisoner) - 1)
    /\ visited \in [Prisoner -> BOOLEAN]
    /\ switchA \in {TRUE, FALSE}
    /\ switchB \in {TRUE, FALSE}

Init ==
    /\ count = 0
    /\ visited = [pr \in Prisoner |-> FALSE]
    /\ switchA = FALSE
    /\ switchB = FALSE

Next ==
    LET chosenPrisoner == CHOOSE pr \in Prisoner : TRUE
        in \/ /\ chosenPrisoner = p1
               /\ (switchA => count' = (IF visited[chosenPrisoner] THEN count ELSE count + 1) /\ switchA' = FALSE)
               /\ switchB' = switchB
               /\ visited' = [visited EXCEPT ![chosenPrisoner] = TRUE]
           \/ /\ chosenPrisoner # p1
              /\ (switchA => (IF visited[chosenPrisoner] < 2 THEN visited' = [visited EXCEPT ![chosenPrisoner] = visited[chosenPrisoner] + 1] ELSE visited'))
              /\ switchA' = (IF visited[chosenPrisoner] < 2 THEN switchA ELSE NOT switchA)
              /\ switchB' = NOT switchB
              /\ count' = count

Spec ==
    Init /\ [][Next]_<<count, visited, switchA, switchB>>

CountInvariant ==
    \/ count \in 0..(Cardinality(Prisoner) - 1)

Safety ==
    [](count < Cardinality(Prisoner) => ~(\E pr \in Prisoner : visited[pr] = FALSE))

Liveness ==
    <>(\A pr \in Prisoner : visited[pr])

====