---------------------------- MODULE prisoners ----------------------------

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS N, InitialLightKnown

ASSUME N \in Nat /\ N > 0
ASSUME InitialLightKnown \in BOOLEAN

VARIABLES
    counter,          \* The designated counter prisoner (1..N, where 1 is the counter)
    lightOn,          \* Whether the lamp is on
    visited,          \* Set of prisoners who have visited
    signaled,         \* Function from prisoner to number of times they've signaled
    counterCount,     \* Counter prisoner's count
    victory,          \* Whether victory has been announced
    done              \* Whether the system has terminated

vars == <<counter, lightOn, visited, signaled, counterCount, victory, done>>

\* The counter prisoner is always prisoner 1
CounterPrisoner == 1

\* The threshold for the counter to declare victory
Threshold == IF InitialLightKnown THEN N - 1 ELSE 2 * N - 1

\* Maximum times a non-counter prisoner can signal
MaxSignals == IF InitialLightKnown THEN 1 ELSE 2

Prisoners == 1..N

TypeOK ==
    /\ lightOn \in BOOLEAN
    /\ visited \subseteq Prisoners
    /\ signaled \in [Prisoners -> Nat]
    /\ counterCount \in Nat
    /\ victory \in BOOLEAN
    /\ done \in BOOLEAN

Init ==
    /\ lightOn = FALSE  \* Light starts off (but may be unknown to prisoners in hard variant)
    /\ visited = {}
    /\ signaled = [p \in Prisoners |-> 0]
    /\ counterCount = 0
    /\ victory = FALSE
    /\ done = FALSE

\* Counter prisoner enters the room
CounterEnters ==
    /\ ~victory
    /\ ~done
    /\ lightOn = TRUE
    /\ counterCount' = counterCount + 1
    /\ lightOn' = FALSE
    /\ visited' = visited \cup {CounterPrisoner}
    /\ IF counterCount + 1 >= Threshold
       THEN victory' = TRUE
       ELSE victory' = FALSE
    /\ UNCHANGED <<signaled, done>>

\* Counter enters but light is off - nothing to count
CounterEntersLightOff ==
    /\ ~victory
    /\ ~done
    /\ lightOn = FALSE
    /\ visited' = visited \cup {CounterPrisoner}
    /\ UNCHANGED <<lightOn, signaled, counterCount, victory, done>>

\* Non-counter prisoner enters and can signal (turn light on)
NonCounterSignals(p) ==
    /\ p # CounterPrisoner
    /\ ~victory
    /\ ~done
    /\ lightOn = FALSE
    /\ signaled[p] < MaxSignals
    /\ lightOn' = TRUE
    /\ signaled' = [signaled EXCEPT ![p] = @ + 1]
    /\ visited' = visited \cup {p}
    /\ UNCHANGED <<counterCount, victory, done>>

\* Non-counter prisoner enters but doesn't signal (light already on or max signals reached)
NonCounterNoSignal(p) ==
    /\ p # CounterPrisoner
    /\ ~victory
    /\ ~done
    /\ \/ lightOn = TRUE
       \/ signaled[p] >= MaxSignals
    /\ visited' = visited \cup {p}
    /\ UNCHANGED <<lightOn, signaled, counterCount, victory, done>>

\* Warden selects a prisoner to enter the room
WardenSelects(p) ==
    \/ (p = CounterPrisoner /\ (CounterEnters \/ CounterEntersLightOff))
    \/ (p # CounterPrisoner /\ (NonCounterSignals(p) \/ NonCounterNoSignal(p)))

\* The system terminates after victory
Terminate ==
    /\ victory
    /\ ~done
    /\ done' = TRUE
    /\ UNCHANGED <<lightOn, visited, signaled, counterCount, victory>>

Next ==
    \/ \E p \in Prisoners : WardenSelects(p)
    \/ Terminate

\* Fairness: warden must be fair in selecting prisoners
Fairness == \A p \in Prisoners : WF_vars(WardenSelects(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Terminating condition - system has terminated or is stuck
Terminating == done \/ (victory /\ done)

\* Safety: victory implies all prisoners have visited
VictoryOK == victory => (visited = Prisoners)

\* Liveness: eventually victory is announced
EventualVictory == <>(victory)

==========================================================================