---------------------------- MODULE PrisonersAndSwitches ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners

ASSUME NumPrisoners >= 2

VARIABLES
    switchA,          \* Boolean: TRUE means up, FALSE means down
    switchB,          \* Boolean: used for random flipping by others
    count,            \* Counter prisoner's count of switch A flips seen
    timesFlippedA,    \* Function: timesFlippedA[p] = number of times prisoner p has flipped A up
    visited,          \* Set of prisoners who have visited the room at least once
    declared,         \* Boolean: TRUE when counter declares all have visited
    currentPrisoner   \* The prisoner currently in the room (for fairness modeling)

Prisoners == 1..NumPrisoners

CounterPrisoner == 1  \* Prisoner 1 is designated as the counter

NonCounterPrisoners == Prisoners \ {CounterPrisoner}

vars == <<switchA, switchB, count, timesFlippedA, visited, declared, currentPrisoner>>

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(2 * (NumPrisoners - 1))
    /\ timesFlippedA \in [NonCounterPrisoners -> 0..2]
    /\ visited \subseteq Prisoners
    /\ declared \in BOOLEAN
    /\ currentPrisoner \in Prisoners

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ timesFlippedA = [p \in NonCounterPrisoners |-> 0]
    /\ visited = {}
    /\ declared = FALSE
    /\ currentPrisoner = 1  \* arbitrary initial value

\* Counter prisoner enters the room
CounterEnters ==
    /\ currentPrisoner' = CounterPrisoner
    /\ visited' = visited \cup {CounterPrisoner}
    /\ IF switchA = TRUE
       THEN /\ switchA' = FALSE
            /\ count' = count + 1
            /\ IF count + 1 = 2 * (NumPrisoners - 1)
               THEN declared' = TRUE
               ELSE declared' = declared
            /\ UNCHANGED switchB
       ELSE /\ switchB' = ~switchB
            /\ UNCHANGED <<switchA, count, declared>>
    /\ UNCHANGED timesFlippedA

\* Non-counter prisoner p enters the room
NonCounterEnters(p) ==
    /\ p \in NonCounterPrisoners
    /\ currentPrisoner' = p
    /\ visited' = visited \cup {p}
    /\ IF switchA = FALSE /\ timesFlippedA[p] < 2
       THEN /\ switchA' = TRUE
            /\ timesFlippedA' = [timesFlippedA EXCEPT ![p] = @ + 1]
            /\ UNCHANGED switchB
       ELSE /\ switchB' = ~switchB
            /\ UNCHANGED <<switchA, timesFlippedA>>
    /\ UNCHANGED <<count, declared>>

\* Next state: randomly select a prisoner to enter
Next ==
    \/ CounterEnters
    \/ \E p \in NonCounterPrisoners : NonCounterEnters(p)

\* Fairness: each prisoner must be selected infinitely often
\* We use weak fairness on each prisoner's action
CounterFairness == WF_vars(CounterEnters)

NonCounterFairness == \A p \in NonCounterPrisoners : WF_vars(NonCounterEnters(p))

Fairness == CounterFairness /\ NonCounterFairness

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: If declared, then all prisoners have visited
Safety == declared => (visited = Prisoners)

\* Liveness: Eventually the counter declares
Liveness == <>(declared = TRUE)

\* Invariant combining type correctness and safety
Invariant == TypeOK /\ Safety

=============================================================================