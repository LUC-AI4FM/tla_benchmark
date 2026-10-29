---------------------------- MODULE Prisoners ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Light_Unknown

ASSUME Prisoner # {} /\ IsFiniteSet(Prisoner)
ASSUME Light_Unknown \in BOOLEAN

VARIABLES count, announced, signalled, light, has_visited

vars == <<count, announced, signalled, light, has_visited>>

N == Cardinality(Prisoner)

Counter == CHOOSE p \in Prisoner : TRUE

Others == Prisoner \ {Counter}

MaxSignals == IF Light_Unknown THEN 2 ELSE 1

Target == IF Light_Unknown THEN 2 * N - 1 ELSE N

TypeOK ==
    /\ count \in 0..(2 * N)
    /\ announced \in BOOLEAN
    /\ signalled \in [Others -> 0..2]
    /\ light \in {"on", "off"}
    /\ has_visited \subseteq Prisoner

Init ==
    /\ count = 1
    /\ announced = FALSE
    /\ signalled = [p \in Others |-> 0]
    /\ light \in (IF Light_Unknown THEN {"on", "off"} ELSE {"off"})
    /\ has_visited = {}

CounterVisit ==
    /\ IF light = "on"
         THEN /\ light' = "off"
              /\ count' = count + 1
              /\ announced' = (announced \/ count + 1 >= Target)
         ELSE /\ UNCHANGED <<light, count>>
              /\ announced' = (announced \/ count >= Target)
    /\ UNCHANGED signalled

OtherVisit(p) ==
    /\ IF light = "off" /\ signalled[p] < MaxSignals
         THEN /\ light' = "on"
              /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
         ELSE UNCHANGED <<light, signalled>>
    /\ UNCHANGED <<count, announced>>

Visit(p) ==
    /\ has_visited' = has_visited \cup {p}
    /\ IF p = Counter THEN CounterVisit ELSE OtherVisit(p)

Next == \E p \in Prisoner : Visit(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Prisoner : WF_vars(Visit(p))

Terminating == <>announced

VictoryOK == announced => (has_visited = Prisoner)

=============================================================================