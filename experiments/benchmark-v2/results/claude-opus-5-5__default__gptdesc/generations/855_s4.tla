------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ Counter \in Prisoner
       /\ IsFiniteSet(Prisoner)
       /\ Prisoner \ {Counter} # {}

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp,      \* TRUE iff switch A is up
          switchBUp,      \* TRUE iff switch B is up
          timesSwitched,  \* times each non-counter prisoner moved switch A up
          count,          \* the counter's count
          visited         \* history variable: prisoners who have entered the room

vars == <<switchAUp, switchBUp, timesSwitched, count, visited>>

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(2 * Cardinality(OtherPrisoner) + 1)
  /\ visited \subseteq Prisoner

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0
  /\ visited = {}

\* The counter declares that everyone has visited when this holds.
Done == count >= 2 * Cardinality(OtherPrisoner)

CounterStep ==
  /\ visited' = visited \cup {Counter}
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched

NonCounterStep(i) ==
  /\ visited' = visited \cup {i}
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count

Next == CounterStep \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: when completion is declared, every prisoner has visited the room.
Safety == Done => (visited = Prisoner)

\* Liveness: the declaration condition is eventually reached.
Liveness == <>Done

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================