---------------------------- MODULE PrisonersAndSwitches ----------------------------

EXTENDS Naturals, TLC

CONSTANTS N, Counter

ASSUME N \in Nat /\ N >= 2
ASSUME Counter \in 1..N

VARIABLES A, B, count, upsUsed, visited, declared

P == 1..N

TypeOK ==
  /\ A \in BOOLEAN
  /\ B \in BOOLEAN
  /\ count \in Nat /\ count <= 2*(N-1)
  /\ upsUsed \in [P -> 0..2]
  /\ visited \in [P -> BOOLEAN]
  /\ declared \in BOOLEAN

AllVisited == \A p \in P: visited[p]

Done == count = 2*(N-1)

Safety == declared => AllVisited

Init ==
  /\ A = FALSE
  /\ B = FALSE
  /\ count = 0
  /\ upsUsed = [p \in P |-> 0]
  /\ visited = [p \in P |-> FALSE]
  /\ declared = FALSE

NonCounterUp(p) ==
  /\ p \in P \ {Counter}
  /\ ~A
  /\ upsUsed[p] < 2
  /\ A' = TRUE
  /\ B' = B
  /\ upsUsed' = [upsUsed EXCEPT ![p] = @ + 1]
  /\ count' = count
  /\ declared' = declared
  /\ visited' = [visited EXCEPT ![p] = TRUE]

NonCounterFlipB(p) ==
  /\ p \in P \ {Counter}
  /\ A \/ upsUsed[p] >= 2
  /\ A' = A
  /\ B' = ~B
  /\ upsUsed' = upsUsed
  /\ count' = count
  /\ declared' = declared
  /\ visited' = [visited EXCEPT ![p] = TRUE]

NonCounterStep(p) ==
  NonCounterUp(p) \/ NonCounterFlipB(p)

CounterConsume ==
  /\ A
  /\ A' = FALSE
  /\ B' = B
  /\ count' = count + 1
  /\ declared' = declared \/ (count + 1 = 2*(N-1))
  /\ upsUsed' = upsUsed
  /\ visited' = [visited EXCEPT ![Counter] = TRUE]

CounterFlipB ==
  /\ ~A
  /\ A' = A
  /\ B' = ~B
  /\ count' = count
  /\ declared' = declared
  /\ upsUsed' = upsUsed
  /\ visited' = [visited EXCEPT ![Counter] = TRUE]

CounterStep ==
  CounterConsume \/ CounterFlipB

Step(p) ==
  IF p = Counter THEN CounterStep ELSE NonCounterStep(p)

Next ==
  \E p \in P: Step(p)

vars == << A, B, count, upsUsed, visited, declared >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in P : WF_vars(Step(p))

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => <>Done

====================================================================================