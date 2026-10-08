MODULE PrisonersPuzzle
EXTENDS Naturals, SETS

CONSTANTS Prisoners, Counter

NonCounter == Prisoners \ {Counter}

VARIABLES A, B, count, visited, upCount, declared

Init ==
  /\ A = FALSE
  /\ B = FALSE
  /\ count = 0
  /\ visited = {}
  /\ upCount = [p ∈ Prisoners |-> 0]
  /\ declared = FALSE

CounterEnter ==
  /\ A' = IF A THEN FALSE ELSE A
  /\ count' = IF A THEN count + 1 ELSE count
  /\ visited' = visited ∪ {Counter}
  /\ upCount' = upCount
  /\ B' = B
  /\ declared' = (count' >= 2 * #NonCounter)

NonCounterEnter(p) ==
  /\ p \in NonCounter
  /\ visited' = visited ∪ {p}
  /\ IF A = FALSE /\ upCount[p] < 2 THEN
        /\ A' = TRUE
        /\ upCount'[p] = upCount[p] + 1
        /\ B' = B
      ELSE
        /\ A' = A
        /\ B' = NOT B
        /\ upCount' = upCount
  /\ count' = count
  /\ declared' = (count >= 2 * #NonCounter)

Next ==
  CounterEnter \/ \E p \in NonCounter : NonCounterEnter(p)

Fairness ==
  WEAK FAIRNESS CounterEnter
  /\ \A p \in NonCounter : WEAK FAIRNESS (NonCounterEnter(p))

Spec == Init /\ [][Next]_<<A, B, count, visited, upCount, declared>> /\ Fairness

SafetyInvariant ==
  declared => visited = Prisoners

LivenessProperty ==
  <> declared

THEOREM SpecImpliesSafety == Spec => [] SafetyInvariant
THEOREM SpecEventuallyDeclared == Spec => LivenessProperty