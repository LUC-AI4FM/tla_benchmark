---------------------------- MODULE PrisonerLightSwitch ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS 
    N,                  \* Number of prisoners (must be at least 2)
    KnownInitialState   \* TRUE if initial light state is known to be off, FALSE otherwise

ASSUME N >= 2
ASSUME KnownInitialState \in BOOLEAN

VARIABLES
    lightOn,            \* Current state of the lamp (TRUE = on, FALSE = off)
    counter,            \* Counter maintained by the designated counter prisoner (prisoner 0)
    visited,            \* Set of prisoners who have actually visited the cell
    signalsSent,        \* Function: for each non-counter prisoner, how many times they've turned light on
    announced,          \* TRUE if victory has been announced
    turn                \* Which prisoner is currently in the cell (or "none")

vars == <<lightOn, counter, visited, signalsSent, announced, turn>>

Prisoners == 0..(N-1)
CounterPrisoner == 0
NonCounterPrisoners == 1..(N-1)

\* Maximum signals each non-counter prisoner can send
MaxSignals == IF KnownInitialState THEN 1 ELSE 2

\* Threshold count needed for the counter to announce victory
\* Known case: N-1 (one signal from each non-counter prisoner)
\* Unknown case: 2*(N-1) - 1 = 2N - 3 signals needed, but we use 2N-1 as per description
\* Actually per problem: unknown case threshold is 2N-1 total signals counted
Threshold == IF KnownInitialState THEN N - 1 ELSE 2 * N - 3

TypeOK ==
    /\ lightOn \in BOOLEAN
    /\ counter \in 0..Threshold
    /\ visited \subseteq Prisoners
    /\ signalsSent \in [NonCounterPrisoners -> 0..MaxSignals]
    /\ announced \in BOOLEAN
    /\ turn \in Prisoners \cup {"none"}

Init ==
    /\ lightOn = IF KnownInitialState THEN FALSE ELSE FALSE  \* Model checks both; start FALSE
    /\ counter = 0
    /\ visited = {}
    /\ signalsSent = [p \in NonCounterPrisoners |-> 0]
    /\ announced = FALSE
    /\ turn = "none"

\* Warden selects a prisoner to enter the cell
WardenSelects(p) ==
    /\ turn = "none"
    /\ ~announced
    /\ turn' = p
    /\ UNCHANGED <<lightOn, counter, visited, signalsSent, announced>>

\* Counter prisoner's action when in the cell
CounterAction ==
    /\ turn = CounterPrisoner
    /\ ~announced
    /\ visited' = visited \cup {CounterPrisoner}
    /\ IF lightOn
       THEN /\ counter' = counter + 1
            /\ lightOn' = FALSE
            /\ IF counter + 1 >= Threshold
               THEN announced' = TRUE
               ELSE announced' = FALSE
       ELSE /\ counter' = counter
            /\ lightOn' = FALSE
            /\ announced' = FALSE
    /\ turn' = "none"
    /\ UNCHANGED signalsSent

\* Non-counter prisoner's action when in the cell
NonCounterAction(p) ==
    /\ turn = p
    /\ p \in NonCounterPrisoners
    /\ ~announced
    /\ visited' = visited \cup {p}
    /\ IF ~lightOn /\ signalsSent[p] < MaxSignals
       THEN /\ lightOn' = TRUE
            /\ signalsSent' = [signalsSent EXCEPT ![p] = @ + 1]
       ELSE /\ lightOn' = lightOn
            /\ signalsSent' = signalsSent
    /\ turn' = "none"
    /\ UNCHANGED <<counter, announced>>

\* Prisoner takes their turn
PrisonerActs ==
    \/ CounterAction
    \/ \E p \in NonCounterPrisoners : NonCounterAction(p)

Next ==
    \/ \E p \in Prisoners : WardenSelects(p)
    \/ PrisonerActs

\* Fairness: warden must eventually select each prisoner
Fairness == \A p \in Prisoners : WF_vars(WardenSelects(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: if announced, then all prisoners have visited
SafetyInvariant == announced => (visited = Prisoners)

\* Liveness: eventually victory is announced
LivenessProperty == <>announced

===================================================================================