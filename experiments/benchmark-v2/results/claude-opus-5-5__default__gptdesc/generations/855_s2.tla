------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME
  /\ IsFiniteSet(Prisoner)
  /\ Counter \in Prisoner
  /\ Prisoner # {Counter}

OtherPrisoner == Prisoner \ {Counter}

N == Cardinality(Prisoner)

VARIABLES
  switchAUp,      \* state of switch A
  switchBUp,      \* state of switch B
  timesSwitched,  \* number of times each non-counter has moved switch A up
  count,          \* the counter's count
  hasVisited      \* ghost variable: set of prisoners who have entered the room

vars == <<switchAUp, switchBUp, timesSwitched, count, hasVisited>>

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(2 * N - 1)
  /\ hasVisited \subseteq Prisoner

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0
  /\ hasVisited = {}

Done == count >= 2 * (N - 1)

NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count
  /\ hasVisited' = hasVisited \cup {i}

CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched
  /\ hasVisited' = hasVisited \cup {Counter}

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: when the counter declares completion, everyone has visited. *)
Safety == Done => (hasVisited = Prisoner)

(* Liveness: the declaration condition is eventually reached. *)
Liveness == <>Done

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================