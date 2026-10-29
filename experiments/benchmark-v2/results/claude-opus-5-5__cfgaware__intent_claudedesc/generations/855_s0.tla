------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ Counter \in Prisoner
       /\ Prisoner # {Counter}
       /\ IsFiniteSet(Prisoner)

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

N == Cardinality(Prisoner)

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0 .. (2 * N - 1)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0

Done == count >= 2 * (N - 1) - 1

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
            /\ UNCHANGED switchBUp
            /\ count' = count + 1
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

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN timesSwitched[x] + SumOver(S \ {x})

CountInvariant ==
  LET totalSwitched == SumOver(OtherPrisoner)
      oneIfUp == IF switchAUp THEN 1 ELSE 0
  IN  /\ count + oneIfUp >= totalSwitched
      /\ count + oneIfUp <= totalSwitched + 1

Safety ==
  [](Done => (\A i \in OtherPrisoner : timesSwitched[i] > 0))

Liveness == <>Done

=============================================================================