---------------------------- MODULE Prisoners ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Light_Unknown

ASSUME Prisoner # {} /\ IsFiniteSet(Prisoner)
ASSUME Light_Unknown \in BOOLEAN

Counter == CHOOSE p \in Prisoner : TRUE

N == Cardinality(Prisoner)

Others == Prisoner \ {Counter}

MaxSignals == IF Light_Unknown THEN 2 ELSE 1

Threshold == IF Light_Unknown THEN 2 * N - 1 ELSE N

VARIABLES lightOn, count, signalled, visited, announced

vars == <<lightOn, count, signalled, visited, announced>>

TypeOK ==
    /\ lightOn \in BOOLEAN
    /\ count \in Nat
    /\ signalled \in [Others -> 0..MaxSignals]
    /\ visited \subseteq Prisoner
    /\ announced \in BOOLEAN

Init ==
    /\ IF Light_Unknown THEN lightOn \in BOOLEAN ELSE lightOn = FALSE
    /\ count = 1
    /\ signalled = [p \in Others |-> 0]
    /\ visited = {}
    /\ announced = FALSE

CounterVisit ==
    /\ visited' = visited \cup {Counter}
    /\ signalled' = signalled
    /\ IF lightOn
          THEN /\ lightOn' = FALSE
               /\ count' = count + 1
          ELSE /\ lightOn' = lightOn
               /\ count' = count
    /\ announced' = (count' >= Threshold)

OtherVisit(p) ==
    /\ visited' = visited \cup {p}
    /\ count' = count
    /\ announced' = announced
    /\ IF ~lightOn /\ signalled[p] < MaxSignals
          THEN /\ lightOn' = TRUE
               /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
          ELSE /\ lightOn' = lightOn
               /\ signalled' = signalled

Visit(p) ==
    /\ ~announced
    /\ IF p = Counter THEN CounterVisit ELSE OtherVisit(p)

Done ==
    /\ announced
    /\ UNCHANGED vars

Next == (\E p \in Prisoner : Visit(p)) \/ Done

Fairness == \A p \in Prisoner : WF_vars(Visit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Terminating == <>announced

VictoryOK == announced => (visited = Prisoner)

=============================================================================