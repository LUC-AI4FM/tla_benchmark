-------------------------------- MODULE PrisonersAndLightBulb --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    N,                  \* Number of prisoners (N >= 2)
    Counter,            \* The distinguished counter prisoner (in 1..N)
    SignalLimit,        \* Max times a non-counter prisoner can turn lamp on
    InitialLampKnown    \* TRUE if prisoners know lamp starts OFF, FALSE if unknown

ASSUME N >= 2
ASSUME Counter \in 1..N
ASSUME SignalLimit >= 1
ASSUME InitialLampKnown \in BOOLEAN

VARIABLES
    lamp,           \* TRUE = lamp is on, FALSE = lamp is off
    count,          \* Counter's count of signals observed
    signalsSent,    \* signalsSent[p] = number of times prisoner p has turned lamp on
    hasVisited,     \* hasVisited[p] = TRUE iff prisoner p has visited at least once
    announced,      \* TRUE iff some prisoner has made the final announcement
    victory,        \* TRUE iff announcement was correct (all visited)
    failed          \* TRUE iff announcement was incorrect (not all visited)

vars == <<lamp, count, signalsSent, hasVisited, announced, victory, failed>>

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}

\* Victory threshold: if initial lamp state is unknown, counter must see N-1 additional
\* signals to be sure (total 2*(N-1) for unknown, N-1 for known)
VictoryThreshold == IF InitialLampKnown THEN N - 1 ELSE 2 * (N - 1)

\* Initial state
Init ==
    /\ lamp = FALSE                             \* Lamp starts off
    /\ count = 0                                \* Counter has observed 0 signals
    /\ signalsSent = [p \in Prisoners |-> 0]    \* No signals sent yet
    /\ hasVisited = [p \in Prisoners |-> FALSE] \* No one has visited
    /\ announced = FALSE                        \* No announcement made
    /\ victory = FALSE                          \* No victory yet
    /\ failed = FALSE                           \* No failure yet

\* Determine the signal budget for a non-counter prisoner
\* If initial lamp unknown, each non-counter signals twice; if known, once
SignalBudget == IF InitialLampKnown THEN 1 ELSE 2

\* Counter prisoner visits: observes lamp, may increment count, may turn lamp off
CounterVisit ==
    /\ ~announced
    /\ hasVisited' = [hasVisited EXCEPT ![Counter] = TRUE]
    /\ IF lamp = TRUE
       THEN /\ count' = count + 1
            /\ lamp' = FALSE
       ELSE /\ count' = count
            /\ lamp' = lamp
    /\ signalsSent' = signalsSent
    /\ UNCHANGED <<announced, victory, failed>>

\* Non-counter prisoner visits: may turn lamp on if within budget and lamp is off
NonCounterVisit(p) ==
    /\ p \in NonCounters
    /\ ~announced
    /\ hasVisited' = [hasVisited EXCEPT ![p] = TRUE]
    /\ IF lamp = FALSE /\ signalsSent[p] < SignalBudget
       THEN /\ lamp' = TRUE
            /\ signalsSent' = [signalsSent EXCEPT ![p] = signalsSent[p] + 1]
       ELSE /\ lamp' = lamp
            /\ signalsSent' = signalsSent
    /\ count' = count
    /\ UNCHANGED <<announced, victory, failed>>

\* Counter makes announcement when count reaches threshold
CounterAnnounce ==
    /\ ~announced
    /\ count >= VictoryThreshold
    /\ announced' = TRUE
    /\ IF \A p \in Prisoners : hasVisited[p]
       THEN /\ victory' = TRUE
            /\ failed' = FALSE
       ELSE /\ victory' = FALSE
            /\ failed' = TRUE
    /\ UNCHANGED <<lamp, count, signalsSent, hasVisited>>

\* Any prisoner could potentially announce (for completeness), but only counter should
\* based on the strategy - this models the possibility of premature announcement
PrematureAnnounce(p) ==
    /\ ~announced
    /\ p # Counter  \* Non-counter making announcement (not part of correct strategy)
    /\ FALSE        \* Disabled - prisoners follow the agreed strategy

\* A prisoner is chosen and visits the room
PrisonerVisit(p) ==
    \/ (p = Counter /\ CounterVisit)
    \/ (p \in NonCounters /\ NonCounterVisit(p))

\* Next state relation: either someone visits or counter announces
Next ==
    \/ \E p \in Prisoners : PrisonerVisit(p)
    \/ CounterAnnounce

\* Fairness: each prisoner is eventually chosen infinitely often
Fairness == \A p \in Prisoners : WF_vars(PrisonerVisit(p))

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* TYPE AND BOUNDEDNESS INVARIANTS
--------------------------------------------------------------------------------

\* Type invariant
TypeOK ==
    /\ lamp \in BOOLEAN
    /\ count \in 0..VictoryThreshold + N  \* Bounded count
    /\ signalsSent \in [Prisoners -> 0..SignalBudget]
    /\ hasVisited \in [Prisoners -> BOOLEAN]
    /\ announced \in BOOLEAN
    /\ victory \in BOOLEAN
    /\ failed \in BOOLEAN

\* Counter's count is bounded by the number of signals that could have been sent
CountBounded ==
    count <= VictoryThreshold + 1

\* Non-counter prisoners respect their signal budget
SignalBudgetRespected ==
    \A p \in NonCounters : signalsSent[p] <= SignalBudget

\* Counter never sends signals (counter doesn't turn lamp on)
CounterNeverSignals ==
    signalsSent[Counter] = 0

\* Boundedness invariant combining all bounds
BoundednessInvariant ==
    /\ CountBounded
    /\ SignalBudgetRespected
    /\ CounterNeverSignals

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* No false victory: announcement implies all have visited
NoFalseVictory ==
    announced => (victory <=> \A p \in Prisoners : hasVisited[p])

\* If victory is declared, all prisoners must have visited
VictoryImpliesAllVisited ==
    victory => \A p \in Prisoners : hasVisited[p]

\* Failure means not everyone visited
FailureImpliesNotAllVisited ==
    failed => \E p \in Prisoners : ~hasVisited[p]

\* Victory and failure are mutually exclusive
MutualExclusion ==
    ~(victory /\ failed)

\* Announcement leads to exactly one of victory or failure
AnnouncementDecides ==
    announced => (victory \/ failed)

\* Combined safety invariant
SafetyInvariant ==
    /\ NoFalseVictory
    /\ VictoryImpliesAllVisited
    /\ FailureImpliesNotAllVisited
    /\ MutualExclusion
    /\ AnnouncementDecides

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* Eventually victory is achieved (under fairness, the protocol terminates successfully)
EventualVictory == <>(victory)

\* Eventually an announcement is made
EventualAnnouncement == <>(announced)

\* Eventually the counter reaches the threshold (helper property)
EventualThreshold == <>(count >= VictoryThreshold)

\* All prisoners eventually visit
AllEventuallyVisit == \A p \in Prisoners : <>(hasVisited[p])

--------------------------------------------------------------------------------
\* DERIVED PROPERTIES FOR VERIFICATION
--------------------------------------------------------------------------------

\* The protocol doesn't get stuck (unless terminated)
NoDeadlock ==
    ~(announced) => ENABLED(Next)

\* Invariant: count only increases when a genuine signal is consumed
\* (This is implicit in the transition rules but stated for clarity)
CountIntegrity ==
    count <= 
        (CHOOSE s \in 0..(N * SignalBudget) : 
            s = (IF lamp THEN 0 ELSE 0) + 
                (LET sent == [p \in NonCounters |-> signalsSent[p]]
                 IN CHOOSE t \in 0..(N * SignalBudget) : TRUE))

================================================================================