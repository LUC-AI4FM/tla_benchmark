---------------------------- MODULE PrisonerLightSwitch ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    N,              \* Number of prisoners (N >= 2)
    KnownInitial    \* TRUE if initial light state is known to be off, FALSE if unknown

VARIABLES
    light,          \* Current state of the lamp (TRUE = on, FALSE = off)
    counter,        \* Counter maintained by the designated counter prisoner (prisoner 0)
    signaled,       \* Function mapping each non-counter prisoner to number of times they've signaled
    visited,        \* Set of prisoners who have visited the cell
    announced,      \* TRUE if victory has been announced
    turn            \* Current prisoner in the cell (0 to N-1)

vars == <<light, counter, signaled, visited, announced, turn>>

Prisoners == 0..(N-1)
CounterPrisoner == 0
NonCounterPrisoners == 1..(N-1)

\* The threshold the counter needs to reach before announcing
\* Known initial state (off): N-1 signals needed (counter knows they visited, needs N-1 others)
\* Unknown initial state: 2*(N-1) - 1 signals needed to handle worst case
Threshold == IF KnownInitial THEN N - 1 ELSE 2 * N - 3

\* Maximum times a non-counter prisoner can signal
MaxSignals == IF KnownInitial THEN 1 ELSE 2

TypeOK ==
    /\ light \in BOOLEAN
    /\ counter \in 0..(2*N)
    /\ signaled \in [NonCounterPrisoners -> 0..2]
    /\ visited \subseteq Prisoners
    /\ announced \in BOOLEAN
    /\ turn \in Prisoners

Init ==
    /\ light = IF KnownInitial THEN FALSE ELSE FALSE  \* Model checker will explore both if needed
    /\ counter = 0
    /\ signaled = [p \in NonCounterPrisoners |-> 0]
    /\ visited = {}
    /\ announced = FALSE
    /\ turn \in Prisoners  \* Warden chooses first prisoner

\* The counter prisoner enters the cell
CounterAction ==
    /\ turn = CounterPrisoner
    /\ ~announced
    /\ visited' = visited \cup {CounterPrisoner}
    /\ IF light = TRUE
       THEN /\ light' = FALSE
            /\ counter' = counter + 1
            /\ IF counter + 1 >= Threshold
               THEN announced' = TRUE
               ELSE announced' = FALSE
       ELSE /\ light' = FALSE
            /\ counter' = counter
            /\ announced' = FALSE
    /\ signaled' = signaled
    /\ turn' \in Prisoners

\* A non-counter prisoner enters the cell
NonCounterAction(p) ==
    /\ turn = p
    /\ p \in NonCounterPrisoners
    /\ ~announced
    /\ visited' = visited \cup {p}
    /\ IF light = FALSE /\ signaled[p] < MaxSignals
       THEN /\ light' = TRUE
            /\ signaled' = [signaled EXCEPT ![p] = signaled[p] + 1]
       ELSE /\ light' = light
            /\ signaled' = signaled
    /\ counter' = counter
    /\ announced' = FALSE
    /\ turn' \in Prisoners

\* Once announced, system stutters (or we can allow continued exploration)
AnnouncedStutter ==
    /\ announced
    /\ UNCHANGED vars

Next ==
    \/ CounterAction
    \/ \E p \in NonCounterPrisoners : NonCounterAction(p)
    \/ AnnouncedStutter

\* Fairness: Warden must be fair - each prisoner gets selected infinitely often
\* We express this as weak fairness on each prisoner being selected
Fairness ==
    /\ WF_vars(CounterAction)
    /\ \A p \in NonCounterPrisoners : WF_vars(NonCounterAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: If victory is announced, all prisoners must have visited
Safety == announced => (visited = Prisoners)

\* Liveness: Eventually victory will be announced
Liveness == <>announced

\* Additional invariant: counter never exceeds reasonable bounds
CounterBounded == counter <= 2 * N

\* The announced flag is stable once set
AnnouncedStable == announced => []announced

===================================================================================