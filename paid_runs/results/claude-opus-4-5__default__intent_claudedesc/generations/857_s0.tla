---------------------------- MODULE PrisonerLamp ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    N,                  \* Number of prisoners (must be >= 2)
    KnownOff            \* TRUE if lamp initial state is known to be off, FALSE if unknown

ASSUME N >= 2
ASSUME KnownOff \in BOOLEAN

VARIABLES
    lamp,               \* Current state of the lamp: TRUE = on, FALSE = off
    counter,            \* Counter maintained by the designated counter prisoner (prisoner 0)
    signalCount,        \* signalCount[p] = number of times prisoner p has signaled (turned lamp on)
    visited,            \* visited[p] = TRUE if prisoner p has ever visited the cell
    currentPrisoner,    \* The prisoner currently in the cell (or "none" if between visits)
    declared,           \* TRUE if victory has been declared
    won                 \* TRUE if declaration was correct (all visited), FALSE if incorrect

vars == <<lamp, counter, signalCount, visited, currentPrisoner, declared, won>>

Prisoners == 0..(N-1)
CounterPrisoner == 0                    \* Prisoner 0 is the designated counter
NonCounterPrisoners == 1..(N-1)

\* Maximum signals each non-counter prisoner can send
MaxSignals == IF KnownOff THEN 1 ELSE 2

\* Threshold for counter to declare victory
\* Known-off: N-1 signals from others + counter's own visit = N total
\* Unknown: (N-1)*2 signals needed, threshold is 2N-1 (counter counts N-1 for themselves implicitly)
Threshold == IF KnownOff THEN N - 1 ELSE 2 * N - 1

TypeOK ==
    /\ lamp \in BOOLEAN
    /\ counter \in 0..Threshold
    /\ signalCount \in [NonCounterPrisoners -> 0..MaxSignals]
    /\ visited \in [Prisoners -> BOOLEAN]
    /\ currentPrisoner \in Prisoners \cup {"none"}
    /\ declared \in BOOLEAN
    /\ won \in BOOLEAN

Init ==
    /\ lamp = IF KnownOff THEN FALSE ELSE FALSE  \* Lamp starts off (but in unknown case, strategy accounts for uncertainty)
    /\ counter = 0
    /\ signalCount = [p \in NonCounterPrisoners |-> 0]
    /\ visited = [p \in Prisoners |-> FALSE]
    /\ currentPrisoner = "none"
    /\ declared = FALSE
    /\ won = FALSE

\* Warden selects a prisoner to visit the cell
SelectPrisoner(p) ==
    /\ ~declared
    /\ currentPrisoner = "none"
    /\ p \in Prisoners
    /\ currentPrisoner' = p
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<lamp, counter, signalCount, declared, won>>

\* Counter prisoner's action in the cell
CounterAction ==
    /\ ~declared
    /\ currentPrisoner = CounterPrisoner
    /\ IF lamp = TRUE
       THEN
           \* Turn lamp off and increment counter
           /\ lamp' = FALSE
           /\ counter' = counter + 1
           /\ IF counter + 1 >= Threshold
              THEN
                  \* Declare victory
                  /\ declared' = TRUE
                  /\ won' = (\A q \in Prisoners : visited[q])
              ELSE
                  /\ UNCHANGED <<declared, won>>
       ELSE
           \* Lamp is off, do nothing with lamp or counter
           /\ UNCHANGED <<lamp, counter, declared, won>>
    /\ currentPrisoner' = "none"
    /\ UNCHANGED <<signalCount, visited>>

\* Non-counter prisoner's action in the cell
NonCounterAction(p) ==
    /\ ~declared
    /\ currentPrisoner = p
    /\ p \in NonCounterPrisoners
    /\ IF lamp = FALSE /\ signalCount[p] < MaxSignals
       THEN
           \* Turn lamp on (signal)
           /\ lamp' = TRUE
           /\ signalCount' = [signalCount EXCEPT ![p] = signalCount[p] + 1]
       ELSE
           \* Either lamp is on or already signaled max times, do nothing
           /\ UNCHANGED <<lamp, signalCount>>
    /\ currentPrisoner' = "none"
    /\ UNCHANGED <<counter, visited, declared, won>>

\* Combined prisoner action (whoever is in the cell acts)
PrisonerActs ==
    \/ CounterAction
    \/ \E p \in NonCounterPrisoners : NonCounterAction(p)

Next ==
    \/ \E p \in Prisoners : SelectPrisoner(p)
    \/ PrisonerActs

\* Fairness: Warden must be fair - eventually every prisoner gets selected
\* We require weak fairness on selection and strong fairness on each prisoner being selected
Fairness ==
    /\ \A p \in Prisoners : SF_vars(SelectPrisoner(p))
    /\ WF_vars(PrisonerActs)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: If victory is declared, all prisoners must have visited
Safety == declared => (\A p \in Prisoners : visited[p])

\* Alternative safety formulation: victory is never incorrectly declared
SafetyInvariant == declared => won

\* Liveness: Eventually the prisoners win (victory is correctly declared)
Liveness == <>won

\* Additional invariant: won implies declared
WonImpliesDeclared == won => declared

\* The counter never exceeds the threshold
CounterBounded == counter <= Threshold

=============================================================================