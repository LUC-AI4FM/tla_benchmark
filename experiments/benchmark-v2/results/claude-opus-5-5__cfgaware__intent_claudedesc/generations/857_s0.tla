------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,        \* the set of prisoners
          Light_Unknown    \* TRUE iff the initial state of the lamp is unknown

ASSUME Prisoner # {} /\ IsFiniteSet(Prisoner)
ASSUME Light_Unknown \in BOOLEAN

N == Cardinality(Prisoner)

\* The designated counter, agreed upon before the game begins
Counter == CHOOSE p \in Prisoner : TRUE

Others == Prisoner \ {Counter}

\* Number of times a non-counter prisoner may turn the lamp on
MaxSignals == IF Light_Unknown THEN 2 ELSE 1

\* The counter's count starts at 1 (it counts itself).
\* Known-off variant: 1 + (N-1) signals = N.
\* Unknown variant: 1 + 2(N-1) signals = 2N-1.  If some prisoner has never
\* signalled, the count can reach at most 1 + 2(N-2) + 1 = 2N-2 < 2N-1.
Threshold == IF Light_Unknown THEN 2 * N - 1 ELSE N

VARIABLES light,      \* TRUE iff the lamp is on
          count,      \* the counter's tally
          signalled,  \* number of times each non-counter has turned the lamp on
          visited,    \* set of prisoners who have actually visited (history)
          done        \* TRUE iff victory has been declared

vars == <<light, count, signalled, visited, done>>

TypeOK ==
  /\ light \in BOOLEAN
  /\ count \in 0 .. (2 * N + 1)
  /\ signalled \in [Others -> 0 .. MaxSignals]
  /\ visited \subseteq Prisoner
  /\ done \in BOOLEAN

Init ==
  /\ light \in (IF Light_Unknown THEN BOOLEAN ELSE {FALSE})
  /\ count = 1
  /\ signalled = [p \in Others |-> 0]
  /\ visited = {}
  /\ done = FALSE

CounterVisit ==
  /\ IF light
       THEN /\ light' = FALSE
            /\ count' = count + 1
            /\ done' = (count + 1 >= Threshold)
       ELSE /\ UNCHANGED <<light, count>>
            /\ done' = (count >= Threshold)
  /\ UNCHANGED signalled

OtherVisit(p) ==
  /\ IF ~light /\ signalled[p] < MaxSignals
       THEN /\ light' = TRUE
            /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
       ELSE UNCHANGED <<light, signalled>>
  /\ UNCHANGED <<count, done>>

\* The warden places prisoner p in the lamp room
Enter(p) ==
  /\ ~done
  /\ visited' = visited \cup {p}
  /\ IF p = Counter THEN CounterVisit ELSE OtherVisit(p)

\* Once victory is declared the system stutters
Finished ==
  /\ done
  /\ UNCHANGED vars

Next == (\E p \in Prisoner : Enter(p)) \/ Finished

\* Fair warden: every prisoner is eventually selected
Fairness == \A p \in Prisoner : WF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: victory is declared only if every prisoner has visited
VictoryOK == done => (visited = Prisoner)

\* Liveness: the prisoners eventually win
Terminating == <>done

THEOREM Spec => [](TypeOK /\ VictoryOK)
THEOREM Spec => Terminating
=============================================================================