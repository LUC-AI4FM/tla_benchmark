```
MODULE PrisonerPuzzle
IMPORT Integers

CONSTANTS
  Prisoner,
  Light_Unknown

VARIABLES
  count,
  victoryAnnounced,
  signals,
  lampState,
  visited

Init ==
  /\ count = 1
  /\ victoryAnnounced = FALSE
  /\ signals = [p \in (Prisoner \ {Min(Prisoner)}) |-> 0]
  /\ lampState = IF Light_Unknown THEN TRUE ELSE FALSE
  /\ visited = {}

Next ==
  \/ \E p \in Prisoner :
      /\ p = Min(Prisoner)
      /\ lampState = TRUE
      /\ count' = count + 1
      /\ victoryAnnounced' = (IF Light_Unknown THEN count + 1 = 2 * Cardinality(Prisoner) - 1 ELSE count + 1 = Cardinality(Prisoner))
      /\ signals' = signals
      /\ lampState' = FALSE
      /\ visited' = visited \cup {p}
      \/ \E p \in (Prisoner \ {Min(Prisoner)}) :
          /\ lampState = FALSE
          /\ signals[p] < IF Light_Unknown THEN 2 ELSE 1
          /\ count' = count
          /\ victoryAnnounced' = FALSE
          /\ signals' = [signals EXCEPT ![p] = signals[p] + 1]
          /\ lampState' = TRUE
          /\ visited' = visited \cup {p}
      \/ \E p \in Prisoner :
          /\ p /= Min(Prisoner)
          /\ signals[p] = IF Light_Unknown THEN 2 ELSE 1
          /\ count' = count
          /\ victoryAnnounced' = FALSE
          /\ signals' = signals
          /\ lampState' = lampState
          /\ visited' = visited \cup {p}

Spec ==
  Init /\ [][Next]_<<count, victoryAnnounced, signals, lampState, visited>>
  /\ WF_(\E p \in Prisoner : Next)_

Terminating ==
  <>victoryAnnounced

TypeOK ==
  count \in Nat
  /\ victoryAnnounced \in BOOLEAN
  /\ signals \in [Prisoner \ {Min(Prisoner)} -> Nat]
  /\ lampState \in BOOLEAN
  /\ visited \subseteq Prisoner

VictoryOK ==
  (victoryAnnounced => visited = Prisoner)

THEOREM Spec => Terminating
THEOREM Spec => []TypeOK
THEOREM Spec => []VictoryOK
```
Note: The `Min(Prisoner)` expression is used to deterministically designate one prisoner as the counter. This assumes that the set of prisoners has a well-defined minimum element, which may require additional constraints or assumptions depending on the specific model-checking configuration.