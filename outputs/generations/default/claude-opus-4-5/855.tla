---------------------------- MODULE PrisonersAndSwitches ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners, Counter

ASSUME NumPrisoners \in Nat /\ NumPrisoners > 0
ASSUME Counter \in 1..NumPrisoners

VARIABLES
    switchA,        \* Boolean: TRUE = up, FALSE = down
    switchB,        \* Boolean: used for meaningless flips
    count,          \* Counter's count of switch A movements
    timesMovedA,    \* Function: timesMovedA[p] = number of times prisoner p moved A up
    visited,        \* Set of prisoners who have visited
    declared,       \* Boolean: TRUE when counter declares completion
    currentPrisoner \* The prisoner currently in the room (or 0 if none selected yet)

vars == <<switchA, switchB, count, timesMovedA, visited, declared, currentPrisoner>>

Prisoners == 1..NumPrisoners
NonCounters == Prisoners \ {Counter}

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(2 * (NumPrisoners - 1))
    /\ timesMovedA \in [Prisoners -> 0..2]
    /\ visited \subseteq Prisoners
    /\ declared \in BOOLEAN
    /\ currentPrisoner \in Prisoners \cup {0}

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ timesMovedA = [p \in Prisoners |-> 0]
    /\ visited = {}
    /\ declared = FALSE
    /\ currentPrisoner = 0

\* Counter's behavior when brought into the room
CounterAction ==
    /\ currentPrisoner = Counter
    /\ ~declared
    /\ visited' = visited \cup {Counter}
    /\ IF switchA = TRUE
       THEN /\ switchA' = FALSE
            /\ count' = count + 1
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ count' = count
    /\ timesMovedA' = timesMovedA
    /\ IF count' = 2 * (NumPrisoners - 1)
       THEN declared' = TRUE
       ELSE declared' = FALSE
    /\ currentPrisoner' = currentPrisoner

\* Non-counter prisoner's behavior when brought into the room
NonCounterAction(p) ==
    /\ currentPrisoner = p
    /\ p # Counter
    /\ ~declared
    /\ visited' = visited \cup {p}
    /\ IF switchA = FALSE /\ timesMovedA[p] < 2
       THEN /\ switchA' = TRUE
            /\ timesMovedA' = [timesMovedA EXCEPT ![p] = @ + 1]
            /\ switchB' = switchB
       ELSE /\ switchB' = ~switchB
            /\ switchA' = switchA
            /\ timesMovedA' = timesMovedA
    /\ count' = count
    /\ declared' = declared
    /\ currentPrisoner' = currentPrisoner

\* Select a prisoner to enter the room
SelectPrisoner(p) ==
    /\ ~declared
    /\ currentPrisoner' = p
    /\ UNCHANGED <<switchA, switchB, count, timesMovedA, visited, declared>>

\* Prisoner takes action in the room
PrisonerTakesAction ==
    /\ currentPrisoner # 0
    /\ ~declared
    /\ \/ CounterAction
       \/ \E p \in NonCounters : NonCounterAction(p)

\* After action, reset current prisoner for next selection
ExitRoom ==
    /\ currentPrisoner # 0
    /\ currentPrisoner' = 0
    /\ UNCHANGED <<switchA, switchB, count, timesMovedA, visited, declared>>

\* Combined step: select prisoner, they act, then exit
PrisonerVisit(p) ==
    /\ ~declared
    /\ visited' = visited \cup {p}
    /\ currentPrisoner' = p
    /\ IF p = Counter
       THEN \* Counter's logic
            /\ IF switchA = TRUE
               THEN /\ switchA' = FALSE
                    /\ count' = count + 1
                    /\ switchB' = switchB
               ELSE /\ switchB' = ~switchB
                    /\ switchA' = switchA
                    /\ count' = count
            /\ timesMovedA' = timesMovedA
            /\ IF count' = 2 * (NumPrisoners - 1)
               THEN declared' = TRUE
               ELSE declared' = FALSE
       ELSE \* Non-counter's logic
            /\ IF switchA = FALSE /\ timesMovedA[p] < 2
               THEN /\ switchA' = TRUE
                    /\ timesMovedA' = [timesMovedA EXCEPT ![p] = @ + 1]
                    /\ switchB' = switchB
               ELSE /\ switchB' = ~switchB
                    /\ switchA' = switchA
                    /\ timesMovedA' = timesMovedA
            /\ count' = count
            /\ declared' = FALSE

Next ==
    \/ \E p \in Prisoners : PrisonerVisit(p)
    \/ (declared /\ UNCHANGED vars)

\* Fairness: each prisoner is selected infinitely often
Fairness ==
    /\ \A p \in Prisoners : WF_vars(PrisonerVisit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: when declared, every prisoner has visited
Safety == declared => (visited = Prisoners)

\* Liveness: eventually the counter declares
Liveness == <>(declared)

===================================================================================