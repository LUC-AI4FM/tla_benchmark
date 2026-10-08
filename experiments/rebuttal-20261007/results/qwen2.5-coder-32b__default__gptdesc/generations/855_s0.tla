------------------------------- MODULE PrisonersAndSwitches -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoners, CounterPrisoner
ASSUME CounterPrisoner \in Prisoners /\ Cardinality(Prisoners) > 1

VARIABLES switchA, switchB, count, visited

Init == 
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ visited = {}

Next ==
    \/ /\ CHOOSE prisoner \in Prisoners : TRUE = CounterPrisoner
       /\ switchA => /\ count' = count + 1
                      /\ switchA' = FALSE
                      /\ switchB' = switchB
                      /\ visited' = visited \cup {CounterPrisoner}
       /\ ~switchA => /\ count' = count
                       /\ switchA' = switchA
                       /\ switchB' = ~switchB
                       /\ visited' = visited \cup {CounterPrisoner}
    \/ /\ CHOOSE prisoner \in Prisoners : TRUE \notin {CounterPrisoner} 
       /\ switchA => /\ IF Cardinality({p \in visited : p \notin {CounterPrisoner}}) < 2
                      THEN count' = count
                           /\ switchA' = FALSE
                           /\ switchB' = switchB
                           /\ visited' = visited \cup {prisoner}
                      ELSE count' = count
                           /\ switchA' = switchA
                           /\ switchB' = ~switchB
                           /\ visited' = visited \cup {prisoner}
       /\ ~switchA => /\ count' = count
                       /\ switchA' = ~switchA
                       /\ switchB' = switchB
                       /\ visited' = visited \cup {prisoner}

Spec ==
    /\ Init
    /\ [][Next]_<<switchA, switchB, count, visited>>
    /\ WF_<<switchA, switchB, count, visited>>(Next)

Safety == 
    \/ count < Cardinality(Prisoners) - 1
    \/ (\E prisoner \in Prisoners : prisoner \notin visited)

Liveness ==
    <>[](count = Cardinality(Prisoners) - 1)

=============================================================================