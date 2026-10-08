---------------------------- MODULE PrisonersAndSwitches ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Prisoner
VARIABLE switchAUp, switchBUp, timesSwitched, count

p2 == CHOOSE p \in Prisoner : p /= Counter
p3 == CHOOSE p \in Prisoner \ {Counter, p2} : TRUE

Counter == CHOOSE p \in Prisoner : TRUE

Spec ==
  /\ switchAUp \in [TRUE, FALSE]
  /\ switchBUp \in [TRUE, FALSE]
  /\ timesSwitched \in [p \in Prisoner \ {Counter} |-> 0..2]
  /\ count \in 0..(2 * (Cardinality(Prisoner) - 1))
  /\ [][
      /\ IF Counter \in Prisoner
        THEN
          /\ switchAUp' = ~switchAUp
          /\ IF switchAUp
            THEN count' = count + 1
            ELSE count' = count
          /\ switchBUp' = ~switchBUp
          /\ timesSwitched' = timesSwitched
        ELSE
          /\ IF ~switchAUp
            THEN
              /\ switchAUp' = TRUE
              /\ timesSwitched' = [timesSwitched EXCEPT ![p] = timesSwitched[p] + 1]
              /\ switchBUp' = switchBUp
              /\ count' = count
            ELSE
              /\ switchAUp' = switchAUp
              /\ timesSwitched' = timesSwitched
              /\ switchBUp' = ~switchBUp
              /\ count' = count
      /\ UNCHANGED <<switchAUp, switchBUp, timesSwitched, count>>
    ]

TypeOK == 
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [Prisoner \ {Counter} -> 0..2]
  /\ count \in 0..(2 * (Cardinality(Prisoner) - 1))

CountInvariant ==
  count = (SUM timesSwitched) + IF switchAUp THEN 0 ELSE 1

Safety == 
  []<>(count = 2 * (Cardinality(Prisoner) - 1)) => [](forall p \in Prisoner \ {Counter} : timesSwitched[p] > 0)

Liveness == 
  <>[]<>(count = 2 * (Cardinality(Prisoner) - 1))

THEOREM Spec => []TypeOK
THEOREM Spec => []CountInvariant
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================