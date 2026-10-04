---------------------------- MODULE PrisonerLightSwitch ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    N,              \* Number of prisoners (must be >= 2)
    KnownInitial    \* TRUE if initial light state is known to be off, FALSE otherwise

ASSUME N >= 2
ASSUME KnownInitial \in BOOLEAN

VARIABLES
    light,          \* Current state of the lamp (TRUE = on, FALSE = off)
    counter,        \* Counter maintained by the designated counter prisoner (prisoner 0)
    visited,        \* Set of prisoners who have actually visited the cell
    signaled,       \* Function: signaled[p] = number of times prisoner p has signaled (turned light on)
    announced,      \* TRUE if victory has been announced
    turn            \* Current prisoner in the cell (or "none" if between turns)

vars == <<light, counter, visited, signaled, announced, turn>>

Prisoners == 0..(N-1)
CounterPrisoner == 0

\* Maximum times a non-counter prisoner can signal
MaxSignals == IF KnownInitial THEN 1 ELSE 2

\* Threshold for counter to announce victory
Threshold == IF KnownInitial THEN N - 1 ELSE 2 * N - 1

TypeOK ==
    /\ light \in BOOLEAN
    /\ counter \in 0..Threshold
    /\ visited \subseteq Prisoners
    /\ signaled \in [Prisoners -> 0..MaxSignals]
    /\ announced \in BOOLEAN
    /\ turn \in Prisoners \cup {"none"}

\* Initial state
Init ==
    /\ light = IF KnownInitial THEN FALSE ELSE FALSE  \* Model checker will explore both if needed
    /\ counter = 0
    /\ visited = {}
    /\ signaled = [p \in Prisoners |-> 0]
    /\ announced = FALSE
    /\ turn = "none"

\* For unknown initial state variant, we also consider light starting as TRUE
InitUnknown ==
    /\ light \in BOOLEAN
    /\ counter = 0
    /\ visited = {}
    /\ signaled = [p \in Prisoners |-> 0]
    /\ announced = FALSE
    /\ turn = "none"

\* Warden selects a prisoner to enter the cell
WardenSelects(p) ==
    /\ turn = "none"
    /\ ~announced
    /\ turn' = p
    /\ visited' = visited \cup {p}
    /\ UNCHANGED <<light, counter, signaled, announced>>

\* Counter prisoner's action in the cell
CounterAction ==
    /\ turn = CounterPrisoner
    /\ ~announced
    /\ IF light = TRUE
       THEN /\ counter' = counter + 1
            /\ light' = FALSE
            /\ IF counter' >= Threshold
               THEN announced' = TRUE
               ELSE announced' = FALSE
       ELSE /\ counter' = counter
            /\ light' = light
            /\ announced' = FALSE
    /\ turn' = "none"
    /\ UNCHANGED <<visited, signaled>>

\* Non-counter prisoner's action in the cell
NonCounterAction(p) ==
    /\ turn = p
    /\ p # CounterPrisoner
    /\ ~announced
    /\ IF light = FALSE /\ signaled[p] < MaxSignals
       THEN /\ light' = TRUE
            /\ signaled' = [signaled EXCEPT ![p] = signaled[p] + 1]
       ELSE /\ light' = light
            /\ signaled' = signaled
    /\ turn' = "none"
    /\ UNCHANGED <<counter, visited, announced>>

\* Prisoner takes action in cell
PrisonerActs ==
    \/ CounterAction
    \/ \E p \in Prisoners \ {CounterPrisoner} : NonCounterAction(p)

\* Next state relation
Next ==
    \/ \E p \in Prisoners : WardenSelects(p)
    \/ PrisonerActs

\* Fairness: warden must be weakly fair in selecting each prisoner
Fairness ==
    \A p \in Prisoners : WF_vars(WardenSelects(p))

\* Full specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Alternative spec for unknown initial state
SpecUnknown == InitUnknown /\ [][Next]_vars /\ Fairness

\* Safety: if victory is announced, all prisoners have visited
Safety == announced => (visited = Prisoners)

\* Liveness: eventually victory is announced
Liveness == <>announced

\* Invariant that should always hold
Inv == TypeOK /\ Safety

===================================================================================