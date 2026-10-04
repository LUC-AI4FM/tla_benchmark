---------------------------- MODULE PrisonersAndSwitches ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS N

ASSUME N > 1

Prisoners == 1..N

Counter == 1

NonCounters == 2..N

VARIABLES
    switchA,
    switchB,
    count,
    contributed,
    visited,
    declared,
    chosen

vars == <<switchA, switchB, count, contributed, visited, declared, chosen>>

TypeOK ==
    /\ switchA \in {0, 1}
    /\ switchB \in {0, 1}
    /\ count \in 0..N
    /\ contributed \in [NonCounters -> 0..2]
    /\ visited \in [Prisoners -> BOOLEAN]
    /\ declared \in BOOLEAN
    /\ chosen \in Prisoners

Init ==
    /\ switchA = 0
    /\ switchB = 0
    /\ count = 0
    /\ contributed = [p \in NonCounters |-> 0]
    /\ visited = [p \in Prisoners |-> FALSE]
    /\ declared = FALSE
    /\ chosen \in Prisoners

NonCounterAction(p) ==
    /\ p \in NonCounters
    /\ chosen = p
    /\ ~declared
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ \/ /\ switchA = 0
          /\ contributed[p] < 2
          /\ switchA' = 1
          /\ contributed' = [contributed EXCEPT ![p] = contributed[p] + 1]
          /\ UNCHANGED <<switchB, count, declared>>
       \/ /\ ~(switchA = 0 /\ contributed[p] < 2)
          /\ switchB' = 1 - switchB
          /\ UNCHANGED <<switchA, contributed, count, declared>>
    /\ chosen' \in Prisoners

CounterAction ==
    /\ chosen = Counter
    /\ ~declared
    /\ visited' = [visited EXCEPT ![Counter] = TRUE]
    /\ \/ /\ switchA = 1
          /\ switchA' = 0
          /\ count' = count + 1
          /\ UNCHANGED <<switchB, contributed, declared>>
       \/ /\ switchA = 0
          /\ switchB' = 1 - switchB
          /\ UNCHANGED <<switchA, count, contributed, declared>>
    /\ chosen' \in Prisoners

Declare ==
    /\ chosen = Counter
    /\ ~declared
    /\ count >= 2 * (N - 1)
    /\ declared' = TRUE
    /\ visited' = [visited EXCEPT ![Counter] = TRUE]
    /\ UNCHANGED <<switchA, switchB, count, contributed>>
    /\ chosen' \in Prisoners

Stutter ==
    /\ declared
    /\ UNCHANGED vars

Next ==
    \/ CounterAction
    \/ Declare
    \/ \E p \in NonCounters : NonCounterAction(p)
    \/ Stutter

Fairness ==
    /\ \A p \in Prisoners : WF_vars(chosen = p /\ ~declared)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TotalContributions == 
    LET Sum[S \in SUBSET NonCounters] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE
             IN contributed[p] + Sum[S \ {p}]
    IN Sum[NonCounters]

AccountingInvariant ==
    /\ count <= TotalContributions
    /\ TotalContributions <= count + switchA

ContributionBound ==
    \A p \in NonCounters : contributed[p] <= 2

VisitedImpliesContributionPossible ==
    \A p \in NonCounters : visited[p] => contributed[p] >= 0

CountBound ==
    count <= 2 * (N - 1)

SafetyInvariant ==
    declared => \A p \in Prisoners : visited[p]

Safety == []SafetyInvariant

Liveness == <>(declared)

AllVisited == \A p \in Prisoners : visited[p]

LivenessAllVisited == <>(AllVisited)

LivenessDeclaration == [](AllVisited ~> declared)

InductiveInvariant ==
    /\ TypeOK
    /\ AccountingInvariant
    /\ ContributionBound
    /\ CountBound
    /\ (count >= 2 * (N - 1) => AllVisited)

=============================================================================