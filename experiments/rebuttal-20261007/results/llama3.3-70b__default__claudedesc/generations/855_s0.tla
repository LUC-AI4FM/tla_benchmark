```tla
MODULE PrisonersAndSwitches

EXTENDS Integers, FiniteSets

CONSTANTS Prisoner, Counter

VARIABLES switchAUp, switchBUp, timesSwitched, count, Done

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [p \in (Prisoner \ {Counter}) |-> 0]
  /\ count = 0
  /\ Done = FALSE

Next ==
  /\ \E p \in Prisoner :
      IF p = Counter
      THEN
        /\ switchAUp' = ~switchAUp
        /\ IF switchAUp THEN count' = count + 1 ELSE count' = count
        /\ switchBUp' = ~switchBUp
        /\ timesSwitched' = timesSwitched
        /\ Done' = (count = 2 * (Cardinality(Prisoner) - 1))
      ELSE
        /\ IF ~switchAUp THEN
            /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![p] = @ + 1]
          ELSE
            /\ switchAUp' = switchAUp
            /\ timesSwitched' = timesSwitched
        /\ IF ~switchAUp THEN switchBUp' = switchBUp ELSE switchBUp' = ~switchBUp
        /\ count' = count
        /\ Done' = Done
  /\ UNCHANGED <<switchAUp, switchBUp, timesSwitched, count, Done>>

Spec ==
  /\ Init
  /\ [][Next]_<<switchAUp, switchBUp, timesSwitched, count, Done>>
  /\ WF_vars(<<Next>>_<<switchAUp, switchBUp, timesSwitched, count, Done>>, Prisoner)

CountInvariant ==
  count = (SUM timesSwitched) + IF switchAUp THEN 1 ELSE 0

Safety ==
  [](Done => \A p \in (Prisoner \ {Counter}) : timesSwitched[p] > 0)

Liveness ==
  <>Done

THEOREM Spec => []CountInvariant
THEOREM Spec => Safety
THEOREM Spec => Liveness

TypeOK == 
  /\ Prisoner \subseteq Nat
  /\ Counter \in Prisoner
  /\ Cardinality(Prisoner) = 4

ModelCheck ==
  /\ TypeOK
  /\ Init
  /\ [][Next]_<<switchAUp, switchBUp, timesSwitched, count, Done>>
  /\ WF_vars(<<Next>>_<<switchAUp, switchBUp, timesSwitched, count, Done>>, Prisoner)
```