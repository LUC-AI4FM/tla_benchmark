---------------------------- MODULE Prisoners ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,       \* the set of participating prisoners
          Light_Unknown   \* TRUE iff the initial state of the lamp is unknown

ASSUME PrisonerNonEmpty == Prisoner # {} /\ IsFiniteSet(Prisoner)
ASSUME LightUnknownBool == Light_Unknown \in BOOLEAN

VARIABLES count,        \* the counter's running count
          announced,    \* whether victory has been announced
          signalled,    \* number of times each non-counter prisoner has signalled
          light,        \* current state of the lamp (TRUE = on)
          has_visited   \* warden's ground-truth set of prisoners who visited

vars == <<count, announced, signalled, light, has_visited>>

N == Cardinality(Prisoner)

\* Deterministically designated counter
Counter == CHOOSE p \in Prisoner : TRUE

Others == Prisoner \ {Counter}

\* Maximum number of signals per non-counter prisoner
MaxSignals == IF Light_Unknown THEN 2 ELSE 1

\* Count required to announce victory
Target == IF Light_Unknown THEN 2 * N - 1 ELSE N

TypeOK ==
    /\ count \in 1..Target
    /\ announced \in BOOLEAN
    /\ signalled \in [Others -> 0..MaxSignals]
    /\ light \in BOOLEAN
    /\ has_visited \subseteq Prisoner

Init ==
    /\ count = 1
    /\ announced = (1 >= Target)  /\ FALSE
    /\ signalled = [p \in Others |-> 0]
    /\ light \in (IF Light_Unknown THEN BOOLEAN ELSE {FALSE})
    /\ has_visited = {}

\* The counter enters the cell
CounterVisit ==
    /\ IF light
         THEN /\ light' = FALSE
              /\ count' = count + 1
              /\ announced' = (announced \/ (count + 1 >= Target))
         ELSE /\ UNCHANGED <<light, count>>
              /\ announced' = (announced \/ (count >= Target))
    /\ UNCHANGED signalled

\* A non-counter prisoner p enters the cell
OtherVisit(p) ==
    /\ IF ~light /\ signalled[p] < MaxSignals
         THEN /\ light' = TRUE
              /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
         ELSE UNCHANGED <<light, signalled>>
    /\ UNCHANGED <<count, announced>>

\* The warden selects prisoner p to visit the cell
Visit(p) ==
    /\ ~announced
    /\ has_visited' = has_visited \cup {p}
    /\ IF p = Counter THEN CounterVisit ELSE OtherVisit(p)

Next == \E p \in Prisoner : Visit(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Prisoner : WF_vars(Visit(p))

\* Safety: an announcement is made only when all prisoners have visited
VictoryOK == announced => (has_visited = Prisoner)

\* Liveness: an announcement is eventually made
Terminating == <>announced

THEOREM Spec => [](TypeOK /\ VictoryOK)
THEOREM Spec => Terminating
=============================================================================