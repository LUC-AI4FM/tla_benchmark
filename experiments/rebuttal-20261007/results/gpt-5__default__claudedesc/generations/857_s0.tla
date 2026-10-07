------------------------------ MODULE LampPrisoners ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    Prisoner,        \* Set of participating prisoners
    Light_Unknown    \* Boolean: whether the lamp's initial state is uncertain

VARIABLES
    cnt,             \* Counter's running count
    announced,       \* Whether a victory announcement has been made
    signals,         \* How many times each non-counter has signalled
    light,           \* Current state of the lamp (TRUE = on, FALSE = off)
    visited          \* Warden's ground-truth record of who has actually visited

vars == << cnt, announced, signals, light, visited >>

Counter == CHOOSE p \in Prisoner : TRUE
NonCounter == Prisoner \ {Counter}

N == Cardinality(Prisoner)
Cap == IF Light_Unknown THEN 2 ELSE 1
Threshold == IF Light_Unknown THEN (2 * N) - 1 ELSE N

Init ==
    /\ cnt = 1
    /\ announced = FALSE
    /\ signals = [p \in NonCounter |-> 0]
    /\ light \in IF Light_Unknown THEN BOOLEAN ELSE {FALSE}
    /\ visited = {}

VisitCounter ==
    /\ ~announced
    /\ light' = FALSE
    /\ cnt' = cnt + IF light THEN 1 ELSE 0
    /\ signals' = signals
    /\ visited' = visited \cup {Counter}
    /\ announced' = announced \/ (cnt' >= Threshold)

VisitNonCounter(p) ==
    /\ ~announced
    /\ p \in NonCounter
    /\ LET doSignal == (~light) /\ (signals[p] < Cap) IN
       /\ light' = IF doSignal THEN TRUE ELSE light
       /\ cnt' = cnt
       /\ signals' = [signals EXCEPT ![p] = IF doSignal THEN @ + 1 ELSE @]
       /\ visited' = visited \cup {p}
       /\ announced' = announced

WardenVisit(p) ==
    IF p = Counter
    THEN VisitCounter
    ELSE VisitNonCounter(p)

Next ==
    \E p \in Prisoner : WardenVisit(p)

Spec ==
    Init
    /\ [][Next]_vars
    /\ \A p \in Prisoner : WF_vars(WardenVisit(p))

TypeOK ==
    /\ cnt \in Nat
    /\ announced \in BOOLEAN
    /\ signals \in [NonCounter -> 0..Cap]
    /\ light \in BOOLEAN
    /\ visited \subseteq Prisoner

VictoryOK ==
    announced => visited = Prisoner

Terminating ==
    <>announced

==============================