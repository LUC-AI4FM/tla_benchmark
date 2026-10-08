```tla
MODULE PrisonersAndLightBulb

EXTENDS Integers, FiniteSets

CONSTANTS N, UnknownLamp, MaxSignals
VARIABLES lamp, visits, signals, counter, announced

Init ==
  /\ lamp = IF UnknownLamp THEN 0 ELSE 0  \* initial lamp state: off or unknown (0)
  /\ visits = [i \in 1..N |-> FALSE]       \* each prisoner has not visited
  /\ signals = [i \in 1..N |-> 0]          \* signal counters for each prisoner
  /\ counter = 0                          \* shared count of visits by the counter prisoner
  /\ announced = FALSE                    \* no announcement made yet

Next ==
  \/ \E i \in 1..N :                       \* choose a prisoner to visit the room
      /\ visits' = [visits EXCEPT ![i] = TRUE]
      /\ signals' = IF (i = 1)             \* counter prisoner increments count if lamp is on
                THEN [signals EXCEPT ![i] = IF lamp = 1 THEN signals[i] + 1 ELSE signals[i]]
                ELSE [signals EXCEPT ![i] = IF lamp = 0 THEN signals[i] + 1 ELSE signals[i]]
      /\ lamp' = IF (i = 1)                \* counter prisoner toggles the lamp
                THEN 1 - lamp
                ELSE IF signals'[i] <= MaxSignals THEN 1 - lamp ELSE lamp
      /\ counter' = IF (i = 1)             \* update shared count if counter prisoner visits
                THEN IF lamp = 1 THEN counter + 1 ELSE counter
                ELSE counter
      /\ announced' = announced
  \/ \E i \in 1..N :                       \* a prisoner makes an announcement
      /\ visits = [j \in 1..N |-> TRUE]    \* all prisoners have visited the room
      /\ announced' = TRUE
      /\ signals' = signals
      /\ lamp' = lamp
      /\ counter' = counter
      /\ visits' = visits

Spec ==
  Init /\ [][Next]_<<lamp, visits, signals, counter, announced>>

SafetyInv ==
  /\ visits \in [1..N -> BOOLEAN]
  /\ signals \in [1..N -> 0..MaxSignals]
  /\ counter \in 0..N
  /\ announced \in BOOLEAN
  /\ (announced => \A i \in 1..N : visits[i])

TypeInv ==
  /\ visits \in [1..N -> BOOLEAN]
  /\ signals \in [1..N -> 0..MaxSignals]
  /\ counter \in 0..N
  /\ announced \in BOOLEAN

BoundednessInv ==
  /\ \A i \in 2..N : signals[i] <= MaxSignals

VictoryThreshold ==
  IF UnknownLamp THEN N + 1 ELSE N

Liveness == <>announced

Fairness == \A i \in 1..N : []<>visits'[i]

THEOREM Spec => []SafetyInv
THEOREM Spec => []TypeInv
THEOREM Spec => []BoundednessInv
THEOREM Spec /\ Fairness => Liveness
```