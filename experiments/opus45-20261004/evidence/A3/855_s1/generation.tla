---------------------------- MODULE PrisonersAndSwitches ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners

ASSUME NumPrisoners >= 2

VARIABLES
    switchA,        \* Boolean: TRUE = up, FALSE = down
    switchB,        \* Boolean: flipped arbitrarily by prisoners
    count,          \* Counter prisoner's count of switch A flips observed
    timesFlippedA,  \* Function: timesFlippedA[p] = number of times prisoner p has flipped A up
    visited,        \* Set of prisoners who have visited the room
    declared,       \* Boolean: TRUE when counter declares all have visited
    currentPrisoner \* The prisoner currently in the room (for fairness)

Prisoners == 1..NumPrisoners

CounterPrisoner == 1

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
    /\ currentPrisoner \in Prisoners

CounterAction ==
    /\ currentPrisoner = CounterPrisoner
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

NonCounterAction(p) ==
    /\ currentPrisoner = p
    /\ p \in NonCounterPrisoners
    /\ visited' = visited \cup {p}
    /\ IF switchA = FALSE /\ timesFlippedA[p] < 2
       THEN /\ switchA' = TRUE
            /\ timesFlippedA' = [timesFlippedA EXCEPT ![p] = @ + 1]
            /\ UNCHANGED switchB
       ELSE /\ switchB' = ~switchB
            /\ UNCHANGED <<switchA, timesFlippedA>>
    /\ UNCHANGED <<count, declared>>

SelectPrisoner ==
    /\ ~declared
    /\ \E p \in Prisoners:
        /\ currentPrisoner' = p
        /\ IF p = CounterPrisoner
           THEN /\ CounterAction
           ELSE /\ NonCounterAction(p)

Terminate ==
    /\ declared
    /\ UNCHANGED vars

Next == SelectPrisoner \/ Terminate

CounterEnters ==
    /\ ~declared
    /\ currentPrisoner' = CounterPrisoner
    /\ CounterAction

NonCounterEnters(p) ==
    /\ ~declared
    /\ p \in NonCounterPrisoners
    /\ currentPrisoner' = p
    /\ NonCounterAction(p)

Fairness ==
    /\ WF_vars(CounterEnters)
    /\ \A p \in NonCounterPrisoners: WF_vars(NonCounterEnters(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == declared => (visited = Prisoners)

Liveness == <>(declared)

=============================================================================