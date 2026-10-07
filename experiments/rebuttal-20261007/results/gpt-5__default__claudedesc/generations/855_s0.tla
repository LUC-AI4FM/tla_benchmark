------------------------------ MODULE PrisonersAndSwitches ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Prisoners, Counter

ASSUME
  /\ IsFiniteSet(Prisoners)
  /\ Counter \in Prisoners
  /\ Cardinality(Prisoners) >= 2

Others == Prisoners \ {Counter}

BoundCount == 2 * Cardinality(Prisoners) - 1
Target == 2 * Cardinality(Others)

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == << switchAUp, switchBUp, timesSwitched, count >>

RECURSIVE Sum(_, _)
Sum(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S: TRUE
    IN f[x] + Sum(S \ {x}, f)

TotalUps == Sum(Others, timesSwitched)

Done == count = Target

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [Others -> 0..2]
  /\ count \in 0..BoundCount

Init ==
  \E f \in [Others -> 0..2]:
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched = f
    /\ count = 0
    /\ count + (IF switchAUp THEN 1 ELSE 0) = Sum(Others, f)

NonCounterAction(p) ==
  p \in Others
  /\ (
       /\ ~switchAUp /\ timesSwitched[p] < 2
       /\ switchAUp' = TRUE
       /\ timesSwitched' = [timesSwitched EXCEPT ![p] = @ + 1]
       /\ UNCHANGED << switchBUp, count >>
     \/
       /\ (switchAUp \/ timesSwitched[p] = 2)
       /\ switchBUp' = ~switchBUp
       /\ UNCHANGED << switchAUp, timesSwitched, count >>
     )

CounterAction ==
  ( /\ switchAUp
    /\ switchAUp' = FALSE
    /\ count' = count + 1
    /\ UNCHANGED << switchBUp, timesSwitched >> )
  \/
  ( /\ ~switchAUp
    /\ switchBUp' = ~switchBUp
    /\ UNCHANGED << switchAUp, timesSwitched, count >> )

PrisonerAction(p) ==
  IF p = Counter THEN CounterAction ELSE NonCounterAction(p)

Next ==
  \E p \in Prisoners: PrisonerAction(p)

CountInvariant ==
  count + (IF switchAUp THEN 1 ELSE 0) = TotalUps

Safety ==
  [](Done => \A p \in Others: timesSwitched[p] >= 1)

Liveness ==
  <>Done

Fairness ==
  \A p \in Prisoners: WF_vars(PrisonerAction(p))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

=============================================================================