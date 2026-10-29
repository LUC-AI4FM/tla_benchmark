------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ Counter \in Prisoner
       /\ Prisoner \ {Counter} # {}
       /\ IsFiniteSet(Prisoner)

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

N == Cardinality(Prisoner)

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(2 * N - 1)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0

FlipB ==
  /\ switchBUp' = ~switchBUp
  /\ UNCHANGED switchAUp

NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ FlipB
            /\ UNCHANGED timesSwitched
  /\ UNCHANGED count

CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ FlipB
            /\ UNCHANGED count
  /\ UNCHANGED timesSwitched

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Done == count = 2 * (N - 1)

Safety == Done => (\A i \in OtherPrisoner : timesSwitched[i] > 0)

Liveness == <>Done

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
==============================================================================