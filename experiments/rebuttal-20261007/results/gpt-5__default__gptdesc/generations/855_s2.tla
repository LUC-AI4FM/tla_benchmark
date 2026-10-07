------------------------------ MODULE PrisonersAndSwitches ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Prisoners, Counter

ASSUME
  /\ Counter \in Prisoners
  /\ IsFiniteSet(Prisoners)
  /\ Cardinality(Prisoners) >= 2

VARIABLES A, B, count, usesRem, visited

DEFINE
  Others == Prisoners \ {Counter}
  Target == 2 * Cardinality(Others)

TypeOK ==
  /\ A \in BOOLEAN
  /\ B \in BOOLEAN
  /\ count \in Nat
  /\ usesRem \in [Others -> 0..2]
  /\ visited \in [Prisoners -> BOOLEAN]

Init ==
  /\ count = 0
  /\ usesRem = [p \in Others |-> 2]
  /\ visited = [p \in Prisoners |-> FALSE]
  /\ A \in BOOLEAN
  /\ B \in BOOLEAN

CounterStep ==
  IF A THEN
    /\ A' = FALSE
    /\ count' = count + 1
    /\ B' = B
  ELSE
    /\ A' = A
    /\ count' = count
    /\ B' = ~B
  /\ visited' = [visited EXCEPT ![Counter] = TRUE]
  /\ usesRem' = usesRem

NonCounterStep(p) ==
  /\ p \in Others
  /\ IF (~A) /\ (usesRem[p] > 0) THEN
       /\ A' = TRUE
       /\ usesRem' = [usesRem EXCEPT ![p] = @ - 1]
       /\ B' = B
     ELSE
       /\ A' = A
       /\ usesRem' = usesRem
       /\ B' = ~B
  /\ count' = count
  /\ visited' = [visited EXCEPT ![p] = TRUE]

Step(p) ==
  /\ p \in Prisoners
  /\ IF p = Counter THEN CounterStep ELSE NonCounterStep(p)

Next ==
  \E p \in Prisoners: Step(p)

Vars == << A, B, count, usesRem, visited >>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A p \in Prisoners: WF_Vars(Step(p))

Done == count = Target

VisitedAll == \A p \in Prisoners: visited[p]

Safety == [](Done => VisitedAll)

Liveness == <>Done

=============================================================================