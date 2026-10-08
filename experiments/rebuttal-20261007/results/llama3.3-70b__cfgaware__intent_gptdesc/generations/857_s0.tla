---------------------------- MODULE PrisonersAndLamp ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, UnknownInitialLamp
VARIABLES prisonersVisited, lamp, counter, signalBudgets, announced

Init ==
  /\ prisonersVisited = {}
  /\ lamp = IF UnknownInitialLamp THEN << >> ELSE FALSE
  /\ counter = 0
  /\ signalBudgets = [i \in 1..N |-> 2]
  /\ announced = FALSE

Next ==
  \/ \E i \in 1..N :
      /\ prisonersVisited' = prisonersVisited \cup {i}
      /\ lamp' = IF (i = 1) /\ (lamp = TRUE) THEN FALSE ELSE lamp
      /\ counter' = IF (i = 1) /\ (lamp = TRUE) THEN counter + 1 ELSE counter
      /\ signalBudgets' = [signalBudgets EXCEPT ![i] = IF (i # 1) /\ (lamp = FALSE) THEN signalBudgets[i] - 1 ELSE signalBudgets[i]]
      /\ announced' = announced
  \/ \E i \in 1..N :
      /\ prisonersVisited' = prisonersVisited
      /\ lamp' = lamp
      /\ counter' = counter
      /\ signalBudgets' = signalBudgets
      /\ announced' = TRUE
      /\ (IF UnknownInitialLamp THEN counter >= N ELSE counter = N)

Spec == Init /\ [][Next]_<<prisonersVisited, lamp, counter, signalBudgets, announced>>

Terminating == <>(announced' = TRUE)

TypeOK ==
  /\ prisonersVisited \in SUBSET Int
  /\ lamp \in BOOLEAN
  /\ counter \in Nat
  /\ signalBudgets \in [1..N -> 0..2]
  /\ announced \in BOOLEAN

VictoryOK == (announced = TRUE) => (Cardinality(prisonersVisited) = N)

THEOREM Spec => []TypeOK
THEOREM Spec => <>Terminating
THEOREM Spec => []VictoryOK
===============================================================================