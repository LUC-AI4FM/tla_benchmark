------------------------------ MODULE PrisonerLightSwitch ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Prisoner,
    Counter,
    LightUnknown

ASSUME PrisonerLightAssumptions ==
    /\ Prisoner # {}
    /\ IsFiniteSet(Prisoner)
    /\ Counter \in Prisoner
    /\ LightUnknown \in BOOLEAN

VARIABLES
    lightOn,
    count,
    timesSignaled,
    visited,
    announced

vars == <<lightOn, count, timesSignaled, visited, announced>>

N == Cardinality(Prisoner)

OtherPrisoner == Prisoner \ {Counter}

SignalLimit == IF LightUnknown THEN 2 ELSE 1

Threshold == IF LightUnknown THEN 2 * N - 1 ELSE N

TypeOK ==
    /\ lightOn \in BOOLEAN
    /\ count \in Nat
    /\ timesSignaled \in [OtherPrisoner -> 0..SignalLimit]
    /\ visited \in [Prisoner -> BOOLEAN]
    /\ announced \in BOOLEAN

Init ==
    /\ lightOn \in (IF LightUnknown THEN BOOLEAN ELSE {FALSE})
    /\ count = 1
    /\ timesSignaled = [p \in OtherPrisoner |-> 0]
    /\ visited = [p \in Prisoner |-> FALSE]
    /\ announced = FALSE

NonCounterVisit(p) ==
    /\ p \in OtherPrisoner
    /\ ~announced
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ IF ~lightOn /\ timesSignaled[p] < SignalLimit
          THEN /\ lightOn' = TRUE
               /\ timesSignaled' = [timesSignaled EXCEPT ![p] = @ + 1]
          ELSE /\ UNCHANGED <<lightOn, timesSignaled>>
    /\ UNCHANGED <<count, announced>>

CounterVisit ==
    /\ ~announced
    /\ visited' = [visited EXCEPT ![Counter] = TRUE]
    /\ LET newCount == IF lightOn THEN count + 1 ELSE count
       IN  /\ count' = newCount
           /\ lightOn' = FALSE
           /\ announced' = (newCount >= Threshold)
    /\ UNCHANGED timesSignaled

Visit(p) ==
    IF p = Counter THEN CounterVisit ELSE NonCounterVisit(p)

Next == \E p \in Prisoner : Visit(p)

Fairness == \A p \in Prisoner : WF_vars(Visit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == announced => \A p \in Prisoner : visited[p]

Liveness == <>announced

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================