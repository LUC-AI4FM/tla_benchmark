----------------------------- MODULE PrisonerLightSwitch -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,                \* Number of prisoners
    Prisoners,        \* Set of prisoners
    Counter,          \* Designated counter prisoner
    UnknownInit       \* BOOLEAN: TRUE => initial light state unknown; FALSE => initially off

ASSUME
    /\ N \in Nat /\ N >= 1
    /\ Counter \in Prisoners
    /\ N = Cardinality(Prisoners)
    /\ UnknownInit \in BOOLEAN

\* Parameters derived from the variant
MaxSig == IF UnknownInit THEN 2 ELSE 1
Threshold == IF UnknownInit THEN (2*N - 1) ELSE N

VARIABLES
    Light,               \* current light state (BOOLEAN)
    Count,               \* number of times the counter has turned the light off
    Visited,             \* set of prisoners who have visited at least once
    SigCount,            \* function Prisoners -> {0,1,..,MaxSig} of how many signals a (non-counter) has made
    CounterSelfSigged,   \* only used when UnknownInit = FALSE: whether counter has performed the single self-signal
    AnnouncedVictory     \* whether victory has been announced

Vars == << Light, Count, Visited, SigCount, CounterSelfSigged, AnnouncedVictory >>

\* Initial states
Init ==
    /\ Light \in (IF UnknownInit THEN BOOLEAN ELSE {FALSE})
    /\ Count = 0
    /\ Visited = {}
    /\ SigCount = [p \in Prisoners |-> 0]
    /\ CounterSelfSigged = FALSE
    /\ AnnouncedVictory = FALSE

\* Counter's step when selected
CounterStep(p) ==
    /\ p = Counter
    /\ Visited' = Visited \cup {p}
    /\ IF (UnknownInit = FALSE) /\ (~CounterSelfSigged) /\ (~Light) THEN
          /\ Light' = TRUE
          /\ CounterSelfSigged' = TRUE
          /\ Count' = Count
       ELSE IF Light THEN
          /\ Light' = FALSE
          /\ CounterSelfSigged' = CounterSelfSigged
          /\ Count' = Count + 1
       ELSE
          /\ UNCHANGED << Light, Count, CounterSelfSigged >>
    /\ AnnouncedVictory' = AnnouncedVictory \/ (Count' >= Threshold)
    /\ SigCount' = SigCount

\* Non-counter's step when selected
NonCounterStep(p) ==
    /\ p \in (Prisoners \ {Counter})
    /\ Visited' = Visited \cup {p}
    /\ IF (~Light) /\ (SigCount[p] < MaxSig) THEN
          /\ Light' = TRUE
          /\ SigCount' = [SigCount EXCEPT ![p] = @ + 1]
       ELSE
          /\ UNCHANGED << Light, SigCount >>
    /\ UNCHANGED << Count, CounterSelfSigged, AnnouncedVictory >>

\* One visit step, chosen by the warden
Visit(p) ==
    /\ p \in Prisoners
    /\ ~AnnouncedVictory
    /\ IF p = Counter
          THEN CounterStep(p)
          ELSE NonCounterStep(p)

Next ==
    \E p \in Prisoners : Visit(p)

Spec ==
    /\ Init
    /\ [][Next]_Vars
    /\ \A p \in Prisoners : WF_Vars(Visit(p))

\* Safety invariants
TypeOK ==
    /\ Light \in BOOLEAN
    /\ Count \in Nat
    /\ Visited \subseteq Prisoners
    /\ SigCount \in [Prisoners -> 0..MaxSig]
    /\ CounterSelfSigged \in BOOLEAN
    /\ AnnouncedVictory \in BOOLEAN

VictoryImpliesAllVisited ==
    AnnouncedVictory => (Visited = Prisoners)

\* Liveness: under weak fairness of selection, victory is eventually announced
EventuallyVictory ==
    <> AnnouncedVictory
=====================================================================================