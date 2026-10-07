---------------------------- MODULE PrisonerLightSwitch ----------------------------

EXTENDS Naturals

CONSTANTS 
    N,          \* number of prisoners, N >= 2
    Counter,    \* the designated counter prisoner, an element of 1..N
    KnownOff    \* BOOLEAN: TRUE = standard variant (initial lamp known OFF), FALSE = unknown variant

ASSUME N \in Nat /\ N >= 2 /\ Counter \in 1..N /\ KnownOff \in BOOLEAN

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}

\* Each non-counter may "signal" (i.e., turn the lamp ON when seeing it OFF) at most once in the KnownOff case,
\* and at most twice in the unknown-initial case.
MaxSignals(p) == IF p = Counter THEN 0 ELSE IF KnownOff THEN 1 ELSE 2

VARIABLES 
    lamp,         \* BOOLEAN: current lamp state (TRUE = ON, FALSE = OFF)
    visited,      \* [Prisoners -> BOOLEAN]: whether each prisoner has visited the cell
    signals,      \* [Prisoners -> 0..2]: how many times each prisoner has signaled (non-counters only)
    tally,        \* Nat: the counter's tally of observed ON->OFF transitions
    victory,      \* BOOLEAN: whether the prisoners have announced victory
    initLampOn    \* BOOLEAN: remembers the initial lamp state (used to set the unknown-case threshold precisely)

vars == << lamp, visited, signals, tally, victory, initLampOn >>

\* Threshold for declaring victory:
\* - Standard (KnownOff = TRUE): N - 1 signals (one per non-counter).
\* - Unknown initial (KnownOff = FALSE): 2N - 2 + (initLampOn ? 1 : 0).
\*   This equals 2N - 1 if the lamp initially happens to be ON, and 2N - 2 if initially OFF,
\*   matching the classic "signal twice" strategy while guaranteeing eventual victory regardless of the initial state.
Threshold == IF KnownOff 
             THEN N - 1 
             ELSE (2 * N - 2) + (IF initLampOn THEN 1 ELSE 0)

TypeOK ==
    /\ lamp \in BOOLEAN
    /\ visited \in [Prisoners -> BOOLEAN]
    /\ signals \in [Prisoners -> 0..2]
    /\ tally \in Nat
    /\ victory \in BOOLEAN
    /\ initLampOn \in BOOLEAN

Init ==
    /\ IF KnownOff THEN lamp = FALSE ELSE lamp \in BOOLEAN
    /\ initLampOn = lamp
    /\ visited = [p \in Prisoners |-> FALSE]
    /\ signals = [p \in Prisoners |-> 0]
    /\ tally = 0
    /\ victory = FALSE

\* A single visit/act by prisoner p.
Step(p) ==
    /\ ~victory
    /\ p \in Prisoners
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ initLampOn' = initLampOn
    /\ IF p = Counter THEN
          /\ signals' = signals
          /\ IF lamp 
                THEN /\ lamp' = FALSE
                     /\ tally' = tally + 1
                ELSE /\ lamp' = lamp
                     /\ tally' = tally
          /\ victory' = victory \/ (tally' >= Threshold)
       ELSE
          /\ tally' = tally
          /\ IF /\ ~lamp
                /\ signals[p] < MaxSignals(p)
                THEN /\ lamp' = TRUE
                     /\ signals' = [signals EXCEPT ![p] = @ + 1]
                ELSE /\ lamp' = lamp
                     /\ signals' = signals
          /\ victory' = victory

Next ==
    \/ ( ~victory /\ (\E p \in Prisoners: Step(p)) )
    \/ ( victory /\ UNCHANGED vars )

\* Weak fairness of the warden's selection: every prisoner is selected infinitely often
\* while victory has not yet been announced.
Fairness == \A p \in Prisoners: WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: any victory announcement implies that all prisoners have actually visited the cell.
AllVisited == \A p \in Prisoners: visited[p]
SafetyInvariant == [](victory => AllVisited)

\* Liveness: under the above weak fairness of selection, the prisoners eventually announce victory.
Liveness == <>victory

================================================================================