---------------------------- MODULE PrisonersLightBulb ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Prisoner,       \* the set of prisoners
          Light_Unknown   \* TRUE iff the initial lamp state is unknown

ASSUME Prisoner # {} /\ IsFiniteSet(Prisoner)
ASSUME Light_Unknown \in BOOLEAN

N == Cardinality(Prisoner)

(* The distinguished counting prisoner, agreed upon beforehand *)
Counter == CHOOSE p \in Prisoner : TRUE

Others == Prisoner \ {Counter}

(* Number of times each non-counter prisoner may switch the lamp on *)
Limit == IF Light_Unknown THEN 2 ELSE 1

(* Count at which the counter announces victory *)
Threshold == IF Light_Unknown THEN 2 * (N - 1) - 1 ELSE N - 1

VARIABLES
    light,      \* the lamp state: TRUE = on, FALSE = off
    count,      \* the counter's private tally
    signalled,  \* signalled[p] = times prisoner p has switched the lamp on
    visited,    \* history variable: prisoners that have visited the room
    announced   \* TRUE once the counter has made the announcement

vars == <<light, count, signalled, visited, announced>>

TypeOK ==
    /\ light \in BOOLEAN
    /\ count \in 0..(2 * N)
    /\ signalled \in [Prisoner -> 0..Limit]
    /\ signalled[Counter] = 0
    /\ visited \subseteq Prisoner
    /\ announced \in BOOLEAN

Init ==
    /\ light \in (IF Light_Unknown THEN BOOLEAN ELSE {FALSE})
    /\ count = 0
    /\ signalled = [p \in Prisoner |-> 0]
    /\ visited = {}
    /\ announced = FALSE

(* A non-counter prisoner visits: switches the lamp on if it is off and
   the prisoner still has signalling budget; otherwise leaves it alone. *)
NonCounterVisit(p) ==
    /\ ~announced
    /\ p # Counter
    /\ visited' = visited \cup {p}
    /\ IF ~light /\ signalled[p] < Limit
         THEN /\ light' = TRUE
              /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
         ELSE UNCHANGED <<light, signalled>>
    /\ UNCHANGED <<count, announced>>

(* The counter visits: if the lamp is on, it switches it off and increments
   its count; it announces once the count has reached the threshold. *)
CounterVisit ==
    LET newCount == IF light THEN count + 1 ELSE count
    IN  /\ ~announced
        /\ visited' = visited \cup {Counter}
        /\ light' = FALSE
        /\ count' = newCount
        /\ announced' = (newCount >= Threshold)
        /\ UNCHANGED signalled

Visit(p) == IF p = Counter THEN CounterVisit ELSE NonCounterVisit(p)

(* After the announcement the game is over *)
Done == announced /\ UNCHANGED vars

Next == (\E p \in Prisoner : Visit(p)) \/ Done

Fairness == \A p \in Prisoner : WF_vars(Visit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: no announcement unless every prisoner has indeed visited *)
VictoryOK == announced => (visited = Prisoner)

(* Boundedness of the counter's tally relative to the signals sent *)
CountBound ==
    count <= (IF Light_Unknown THEN 1 ELSE 0) + 2 * (N - 1)

(* Liveness: eventually a (correct) announcement is made *)
Terminating == <>announced

=============================================================================