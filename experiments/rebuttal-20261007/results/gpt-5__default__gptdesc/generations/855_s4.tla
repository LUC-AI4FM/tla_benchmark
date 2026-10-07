------------------------------ MODULE PrisonersSwitches ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Prisoners, \* A finite nonempty set of prisoner identifiers
  Counter    \* The designated counter, an element of Prisoners

ASSUME Counter \in Prisoners /\ Cardinality(Prisoners) >= 2

VARIABLES
  A,         \* Switch A: TRUE = up, FALSE = down
  B,         \* Switch B: TRUE/FALSE, flipped by prisoners when not acting on A
  count,     \* Counter's tally of times he has found A up (and turned it down)
  raises,    \* Function [Prisoners -> Nat], for non-counters: times they raised A (max 2)
  visits     \* Function [Prisoners -> Nat], times each prisoner has visited the room

vars == << A, B, count, raises, visits >>

Others == Prisoners \ {Counter}
N == Cardinality(Prisoners)
Threshold == 2 * Cardinality(Others)

Init ==
  /\ A = FALSE
  /\ B = FALSE
  /\ count = 0
  /\ raises \in [Prisoners -> Nat]
  /\ raises = [p \in Prisoners |-> 0]
  /\ visits \in [Prisoners -> Nat]
  /\ visits = [p \in Prisoners |-> 0]

CounterStep ==
  /\ visits' = [visits EXCEPT ![Counter] = @ + 1]
  /\ raises' = raises
  /\ IF A
        THEN /\ A' = FALSE
             /\ count' = count + 1
             /\ B' = B
        ELSE /\ A' = A
             /\ count' = count
             /\ B' = ~B

NonCounterStep(p) ==
  /\ p \in Others
  /\ visits' = [visits EXCEPT ![p] = @ + 1]
  /\ count' = count
  /\ IF ~A /\ raises[p] < 2
        THEN /\ A' = TRUE
             /\ B' = B
             /\ raises' = [raises EXCEPT ![p] = @ + 1]
        ELSE /\ A' = A
             /\ B' = ~B
             /\ raises' = raises

Step(p) ==
  /\ p \in Prisoners
  /\ IF p = Counter THEN CounterStep ELSE NonCounterStep(p)

Next ==
  \E p \in Prisoners : Step(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Prisoners : WF_vars(Step(p))

\* Auxiliary state predicates
AllVisited ==
  \A p \in Prisoners : visits[p] > 0

Done ==
  count = Threshold

\* Safety invariants
TypeInv ==
  /\ A \in BOOLEAN
  /\ B \in BOOLEAN
  /\ count \in Nat
  /\ raises \in [Prisoners -> 0..2]
  /\ visits \in [Prisoners -> Nat]

CountBoundInv ==
  count <= Threshold

RaiseBoundInv ==
  \A p \in Others : raises[p] <= 2

\* Stated safety property: when the protocol declares completion, everyone has visited
Safety ==
  [](Done => AllVisited)

\* Stated liveness property: the declaration condition is eventually reached
Liveness ==
  <>Done

=============================================================================