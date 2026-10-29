------------------------------- MODULE Prisoners -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Prisoner,        \* the set of all prisoners (including the counter)
    Counter,         \* the designated counter prisoner
    LightUnknown     \* TRUE: initial lamp state unknown; FALSE: known to be off

ASSUME CounterAssump == Counter \in Prisoner
ASSUME LightAssump   == LightUnknown \in BOOLEAN
ASSUME FiniteAssump  == IsFiniteSet(Prisoner) /\ Prisoner # {}

N == Cardinality(Prisoner)

Others == Prisoner \ {Counter}

\* Number of times each non-counter prisoner may turn the light on
MaxSignals == IF LightUnknown THEN 2 ELSE 1

\* The counter starts with count = 1 (counting himself) and announces
\* once count reaches this threshold.
Threshold == IF LightUnknown THEN 2 * N - 1 ELSE N

VARIABLES
    light,       \* TRUE iff the lamp in the special cell is on
    count,       \* the counter's tally
    signalled,   \* signalled[p]: times non-counter p has turned the light on
    visited,     \* set of prisoners who have actually visited the cell
    announced    \* TRUE iff victory has been announced

vars == <<light, count, signalled, visited, announced>>

TypeOK ==
    /\ light \in BOOLEAN
    /\ count \in Nat
    /\ signalled \in [Others -> 0..MaxSignals]
    /\ visited \subseteq Prisoner
    /\ announced \in BOOLEAN

Init ==
    /\ light \in (IF LightUnknown THEN BOOLEAN ELSE {FALSE})
    /\ count = 1
    /\ signalled = [p \in Others |-> 0]
    /\ visited = {}
    /\ announced = FALSE

\* The counter enters the cell: if light is on, turn it off and increment
\* count; announce victory once the threshold is reached.
CounterEnter ==
    LET nc == IF light THEN count + 1 ELSE count
    IN  /\ ~announced
        /\ visited' = visited \cup {Counter}
        /\ light' = FALSE
        /\ count' = nc
        /\ announced' = (nc >= Threshold)
        /\ UNCHANGED signalled

\* A non-counter prisoner enters: if the light is off and he has not yet
\* signalled the maximum number of times, he turns it on.
OtherEnter(p) ==
    /\ ~announced
    /\ visited' = visited \cup {p}
    /\ IF ~light /\ signalled[p] < MaxSignals
         THEN /\ light' = TRUE
              /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
         ELSE UNCHANGED <<light, signalled>>
    /\ UNCHANGED <<count, announced>>

\* The warden selects prisoner p to visit the cell
Enter(p) == IF p = Counter THEN CounterEnter ELSE OtherEnter(p)

\* After victory the system halts (stuttering to avoid deadlock)
Done == announced /\ UNCHANGED vars

Next == (\E p \in Prisoner : Enter(p)) \/ Done

Fairness == \A p \in Prisoner : WF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: victory is announced only if every prisoner has visited the cell
Safety == announced => (visited = Prisoner)

\* Liveness: the prisoners eventually announce victory
Liveness == <>announced

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================