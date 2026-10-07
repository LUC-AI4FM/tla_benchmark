```tla
MODULE PrisonerPuzzle

EXTENDS Integers, FiniteSets

CONSTANTS Prisoner, Light_Unknown

VARIABLES count, victory, signals, lamp, visited

Init ==
  /\ count = 1
  /\ victory = FALSE
  /\ signals = [p \in (Prisoner \ {<<>>}) |-> 0]
  /\ lamp = IF Light_Unknown THEN TRUE ELSE FALSE
  /\ visited = {}

Next ==
  \/ \E p \in Prisoner:
      /\ visited' = visited \cup {p}
      /\ IF p = <<>> 
        THEN
          /\ count' = IF lamp THEN count + 1 ELSE count
          /\ lamp' = FALSE
          /\ signals' = signals
          /\ victory' = (count = IF Light_Unknown THEN 2 * Cardinality(Prisoner) - 1 ELSE Cardinality(Prisoner))
        ELSE
          /\ count' = count
          /\ lamp' = IF lamp THEN TRUE ELSE (signals'[p] < 2)
          /\ signals' = [signals EXCEPT ![p] = signals[p] + 1]
          /\ victory' = victory
      /\ UNCHANGED <<count, victory, signals, lamp, visited>>

Spec ==
  Init /\ [][Next]_<<count, victory, signals, lamp, visited>>
  /\ WF_<<Prisoner>>(Next)

TypeOK == 
  /\ count \in Nat
  /\ victory \in BOOLEAN
  /\ signals \in [Prisoner \ {<<>>} -> Nat]
  /\ lamp \in BOOLEAN
  /\ visited \subseteq Prisoner

VictoryOK ==
  victory => visited = Prisoner

Terminating == <>victory

THEOREM Spec => []TypeOK
THEOREM Spec => []VictoryOK
THEOREM Spec => Terminating

```
Note: `<<>>` denotes the counter prisoner. The actual value should be replaced with a specific prisoner from the set `Prisoner`.