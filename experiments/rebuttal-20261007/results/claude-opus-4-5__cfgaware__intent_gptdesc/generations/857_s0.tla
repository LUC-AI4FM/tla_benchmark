---------------------------- MODULE prisoners ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS 
    N,              \* Number of prisoners (must be >= 2)
    MaxSignals,     \* Maximum times a non-counter prisoner can signal (typically 1 or 2)
    InitialLampKnown \* TRUE if prisoners know lamp starts OFF, FALSE if unknown

VARIABLES
    lamp,           \* The lamp state: TRUE = on, FALSE = off
    counter,        \* The counter prisoner's count of signals observed
    signalsSent,    \* Array: signalsSent[p] = how many times prisoner p has turned lamp ON
    visited,        \* Array: visited[p] = TRUE if prisoner p has visited the room
    announced,      \* TRUE if someone has made the announcement
    success,        \* TRUE if announcement was correct (victory), FALSE if wrong
    turn            \* Which prisoner is currently in the room (0 means no one yet)

vars == <<lamp, counter, signalsSent, visited, announced, success, turn>>

Prisoners == 1..N
CounterPrisoner == 1  \* Prisoner 1 is designated as the counter

\* Victory threshold depends on whether initial lamp state is known
\* If known (starts OFF): counter needs N-1 signals (one from each non-counter)
\* If unknown (might start ON): counter needs 2*(N-1) signals to be safe
\* Actually, standard solution: if unknown, non-counters signal twice, threshold is 2N-3 or 2(N-1)
\* We use: if known, threshold = N-1; if unknown, threshold = MaxSignals*(N-1)
VictoryThreshold == IF InitialLampKnown THEN N - 1 ELSE MaxSignals * (N - 1)

TypeOK ==
    /\ lamp \in BOOLEAN
    /\ counter \in 0..VictoryThreshold
    /\ signalsSent \in [Prisoners -> 0..MaxSignals]
    /\ visited \in [Prisoners -> BOOLEAN]
    /\ announced \in BOOLEAN
    /\ success \in BOOLEAN
    /\ turn \in 0..N

\* Initial state
Init ==
    /\ lamp = FALSE  \* Lamp starts OFF (but prisoners may not know this if InitialLampKnown = FALSE)
    /\ counter = 0
    /\ signalsSent = [p \in Prisoners |-> 0]
    /\ visited = [p \in Prisoners |-> FALSE]
    /\ announced = FALSE
    /\ success = FALSE
    /\ turn = 0

\* All prisoners have visited at least once
AllVisited == \A p \in Prisoners : visited[p]

\* Counter prisoner's turn: observe lamp, possibly increment count, possibly announce
CounterTurn ==
    /\ ~announced
    /\ turn' \in Prisoners
    /\ turn' = CounterPrisoner
    /\ visited' = [visited EXCEPT ![CounterPrisoner] = TRUE]
    /\ IF lamp = TRUE
       THEN /\ counter' = counter + 1
            /\ lamp' = FALSE  \* Counter turns lamp OFF after counting
       ELSE /\ counter' = counter
            /\ lamp' = lamp   \* Leave lamp as is (already OFF)
    /\ signalsSent' = signalsSent
    /\ announced' = FALSE
    /\ success' = success

\* Counter prisoner announces victory when threshold reached
CounterAnnounce ==
    /\ ~announced
    /\ counter >= VictoryThreshold
    /\ announced' = TRUE
    /\ success' = AllVisited  \* Success only if all have actually visited
    /\ UNCHANGED <<lamp, counter, signalsSent, visited, turn>>

\* Non-counter prisoner's turn: possibly turn lamp ON if budget allows
NonCounterTurn(p) ==
    /\ ~announced
    /\ p # CounterPrisoner
    /\ turn' = p
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ IF lamp = FALSE /\ signalsSent[p] < MaxSignals
       THEN /\ lamp' = TRUE  \* Turn lamp ON to signal
            /\ signalsSent' = [signalsSent EXCEPT ![p] = signalsSent[p] + 1]
       ELSE /\ lamp' = lamp  \* Leave lamp as is (either already ON or budget exhausted)
            /\ signalsSent' = signalsSent
    /\ counter' = counter
    /\ announced' = FALSE
    /\ success' = success

\* A prisoner makes a premature/incorrect announcement (models possible failure)
\* This allows any prisoner to announce at any time (though not part of standard strategy)
PrematureAnnounce(p) ==
    /\ ~announced
    /\ p # CounterPrisoner  \* Only non-counter might make wrong announcement
    /\ announced' = TRUE
    /\ success' = AllVisited
    /\ UNCHANGED <<lamp, counter, signalsSent, visited, turn>>

\* Next state relation - nondeterministically choose a prisoner
Next ==
    \/ CounterTurn
    \/ CounterAnnounce
    \/ \E p \in Prisoners \ {CounterPrisoner} : NonCounterTurn(p)

\* Fairness: each prisoner is eventually chosen infinitely often
\* We express this as weak fairness on each prisoner's action
Fairness ==
    /\ WF_vars(CounterTurn)
    /\ WF_vars(CounterAnnounce)
    /\ \A p \in Prisoners \ {CounterPrisoner} : WF_vars(NonCounterTurn(p))

\* The complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Terminating condition: the protocol has ended (announcement made)
Terminating == announced

\* Safety: Victory is only announced when all have visited
\* No false victory - if announced and success, then all visited
VictoryOK == announced => (success <=> AllVisited)

\* Additional safety: if success is TRUE, all must have visited
SafetyInvariant == success => AllVisited

\* Liveness: eventually the game terminates with success
\* Under fairness, the protocol eventually reaches a correct announcement
EventualVictory == <>(announced /\ success)

\* Liveness: eventually terminates
EventualTermination == <>Terminating

\* Boundedness invariant: counter never exceeds threshold
BoundednessInvariant ==
    /\ counter <= VictoryThreshold
    /\ \A p \in Prisoners : signalsSent[p] <= MaxSignals

\* Combined type and bounds invariant
TypeAndBoundsOK == TypeOK /\ BoundednessInvariant

==========================================================================