-------------------------- MODULE PrisonerLightSwitch --------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N,                 \* The number of prisoners
         CounterPrisoner,     \* The designated prisoner who counts
         InitialLightKnown    \* TRUE if the initial light state is known to be OFF

ASSUME N \in 1..100 /\ N > 1
ASSUME CounterPrisoner \in 1..N
ASSUME InitialLightKnown \in BOOLEAN

Prisoners == 1..N
NonCounters == Prisoners \ {CounterPrisoner}

\* State variables
VARIABLES light_on,           \* TRUE if the light is on, FALSE otherwise
          visited,            \* The set of prisoners who have visited the cell (ground truth)
          signals_sent,       \* A function mapping each non-counter to the number of times they have signaled
          counter_count,      \* The counter's internal count of signals
          victory_announced   \* TRUE if the counter has announced victory

vars == <<light_on, visited, signals_sent, counter_count, victory_announced>>

\* The number of times a non-counter must signal.
SignalLimit == IF InitialLightKnown THEN 1 ELSE 2

\* The number of signals the counter must count before announcing victory.
CountThreshold == IF InitialLightKnown THEN N - 1 ELSE 2 * N - 1

\* The type invariant.
TypeOK ==
    /\ light_on \in BOOLEAN
    /\ visited \subseteq Prisoners
    /\ signals_sent \in [NonCounters -> 0..SignalLimit]
    /\ counter_count \in 0..CountThreshold
    /\ victory_announced \in BOOLEAN

\* The initial state of the system.
Init ==
    /\ IF InitialLightKnown
       THEN light_on = FALSE
       ELSE light_on \in BOOLEAN
    /\ visited = {}
    /\ signals_sent = [p \in NonCounters |-> 0]
    /\ counter_count = 0
    /\ victory_announced = FALSE

\* Action of prisoner `p` being selected by the warden to enter the cell.
\* This action is only enabled as long as victory has not been announced.
Select(p) ==
    /\ \lnot victory_announced
    /\ visited' = visited \cup {p}
    /\ IF p = CounterPrisoner
       THEN (* The counter prisoner's turn *)
            /\ IF light_on
               THEN (* Light is on: turn it off and increment count *)
                    /\ light_on' = FALSE
                    /\ counter_count' = counter_count + 1
                    /\ IF counter_count' = CountThreshold
                       THEN victory_announced' = TRUE
                       ELSE victory_announced' = victory_announced
               ELSE (* Light is off: do nothing *)
                    /\ UNCHANGED <<light_on, counter_count, victory_announced>>
            /\ UNCHANGED <<signals_sent>>
       ELSE (* A non-counter prisoner's turn *)
            /\ IF \lnot light_on /\ signals_sent[p] < SignalLimit
               THEN (* Light is off and can signal: turn it on *)
                    /\ light_on' = TRUE
                    /\ signals_sent' = [signals_sent EXCEPT ![p] = signals_sent[p] + 1]
               ELSE (* Light is on or already signaled enough: do nothing *)
                    /\ UNCHANGED <<light_on, signals_sent>>
            /\ UNCHANGED <<counter_count, victory_announced>>

\* Stuttering step for when victory has been announced.
Done ==
    /\ victory_announced
    /\ UNCHANGED vars

\* The next-state relation.
Next ==
    \/ (\E p \in Prisoners : Select(p))
    \/ Done

\* The main specification.
Spec == Init /\ [][Next]_vars

\* Liveness property: The prisoners eventually announce victory.
Terminating == <>victory_announced

\* Safety property: If victory is announced, all prisoners must have visited the cell.
VictoryOK == [](victory_announced => visited = Prisoners)

=============================================================================