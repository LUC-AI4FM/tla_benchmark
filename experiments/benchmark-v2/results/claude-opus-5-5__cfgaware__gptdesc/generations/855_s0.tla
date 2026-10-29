---------------------------- MODULE Prisoners -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME
  /\ IsFiniteSet(Prisoner)
  /\ Counter \in Prisoner
  /\ Cardinality(Prisoner) > 1

OtherPrisoner == Prisoner \ {Counter}

VARIABLES
  switchAUp,
  switchBUp,
  timesSwitched,
  count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

NumOthers == Cardinality(OtherPrisoner)

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0 .. (2 * NumOthers + 1)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0

NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count

CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Done == count >= 2 * NumOthers

RECURSIVE SumSwitched(_)
SumSwitched(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  timesSwitched[x] + SumSwitched(S \ {x})

totalSwitched == SumSwitched(OtherPrisoner)

oneIfUp == IF switchAUp THEN 1 ELSE 0

CountInvariant ==
  /\ count + oneIfUp >= totalSwitched
  /\ count + oneIfUp <= totalSwitched + 1

Safety == [](Done => \A i \in OtherPrisoner : timesSwitched[i] > 0)

Liveness == <>Done
=============================================================================