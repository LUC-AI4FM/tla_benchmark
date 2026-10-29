---------------------------- MODULE Prisoners -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Counter \in Prisoner
       /\ Prisoner # {Counter}

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp,      \* TRUE iff switch A is up
          switchBUp,      \* TRUE iff switch B is up
          timesSwitched,  \* number of times each non-counter moved switch A up
          count,          \* the counter's tally
          visited         \* ghost: set of prisoners who have been in the room

vars == <<switchAUp, switchBUp, timesSwitched, count, visited>>

TotalNeeded == 2 * Cardinality(Prisoner) - 2

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0 .. (2 * Cardinality(Prisoner) - 1)
  /\ visited \subseteq Prisoner

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0
  /\ visited = {}

Done == count >= TotalNeeded

CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ visited' = visited \cup {Counter}
  /\ UNCHANGED timesSwitched

NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ visited' = visited \cup {i}
  /\ UNCHANGED count

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Safety: when the counter declares completion, every prisoner has visited.
SafetyInv == Done => (visited = Prisoner)

Safety == []SafetyInv

\* Stronger auxiliary invariant relating count to switch activity.
CountInv ==
  LET Sum[S \in SUBSET OtherPrisoner] ==
        IF S = {} THEN 0
        ELSE LET j == CHOOSE j \in S : TRUE
             IN timesSwitched[j] + Sum[S \ {j}]
  IN count + (IF switchAUp THEN 1 ELSE 0) <= Sum[OtherPrisoner] + 1

\* Liveness: the declaration condition is eventually reached.
Liveness == <>Done

THEOREM Spec => [](TypeOK /\ SafetyInv)
THEOREM Spec => Liveness
=============================================================================