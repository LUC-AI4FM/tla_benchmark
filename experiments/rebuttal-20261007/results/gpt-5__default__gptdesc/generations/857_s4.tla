------------------------------ MODULE PrisonerSwitch ------------------------------

EXTENDS Naturals

CONSTANTS
    N,           \* number of prisoners (a positive natural)
    Counter,     \* designated counter prisoner, an element of 1..N
    KnownOff     \* BOOLEAN: TRUE = standard variant (lamp known initially OFF), FALSE = unknown variant

ASSUME /\ N \in Nat \ {0}
       /\ Counter \in 1..N
       /\ KnownOff \in BOOLEAN

VARIABLES
    lampOn,        \* BOOLEAN state of the lamp
    count,         \* how many times the counter has turned the lamp OFF (the counter's tally)
    signalsSent,   \* function [1..N -> Nat], how many times each non-counter has turned the lamp ON
    visited,       \* function [1..N -> BOOLEAN], whether each prisoner has visited at least once
    announced,     \* BOOLEAN, whether the counter has announced victory
    seedUsed       \* BOOLEAN, whether the counter has performed the one-time "seed" (only in unknown variant)

Prisoners == 1..N

\* Limit of ON-signals per non-counter:
SignalLimit(i) == IF i = Counter THEN 0 ELSE IF KnownOff THEN 1 ELSE 2

\* Counter's target threshold:
Threshold == IF KnownOff THEN (N - 1) ELSE (2*N - 1)

TypeOK ==
  /\ lampOn \in BOOLEAN
  /\ count \in Nat
  /\ signalsSent \in [Prisoners -> Nat]
  /\ visited \in [Prisoners -> BOOLEAN]
  /\ announced \in BOOLEAN
  /\ seedUsed \in BOOLEAN

Init ==
  /\ visited = [i \in Prisoners |-> FALSE]
  /\ signalsSent = [i \in Prisoners |-> 0]
  /\ count = 0
  /\ announced = FALSE
  /\ seedUsed = FALSE
  /\ lampOn \in (IF KnownOff THEN {FALSE} ELSE BOOLEAN)

NonCounterCanSignal(i) ==
  /\ i \in Prisoners
  /\ i # Counter
  /\ ~lampOn
  /\ signalsSent[i] < SignalLimit(i)

NonCounterStep(i) ==
  /\ i \in Prisoners
  /\ i # Counter
  /\ visited' = [visited EXCEPT ![i] = TRUE]
  /\ signalsSent' = [signalsSent EXCEPT ![i] = @ + (IF NonCounterCanSignal(i) THEN 1 ELSE 0)]
  /\ lampOn' = IF NonCounterCanSignal(i) THEN TRUE ELSE lampOn
  /\ UNCHANGED <<count, announced, seedUsed>>

Seedable ==
  /\ ~KnownOff
  /\ ~lampOn
  /\ ~seedUsed

CounterStep ==
  \* Deterministic behavior for the counter:
  LET inc == IF lampOn THEN 1 ELSE 0
      newCount == count + inc
      newLampOn ==
        IF lampOn
          THEN FALSE                      \* turn OFF and count
          ELSE IF Seedable
                 THEN TRUE                \* one-time seeding in unknown variant
                 ELSE lampOn              \* no change
      newSeed == IF Seedable THEN TRUE ELSE seedUsed
      newAnnounced == announced \/ (newCount >= Threshold)
  IN
    /\ visited' = [visited EXCEPT ![Counter] = TRUE]
    /\ count' = newCount
    /\ lampOn' = newLampOn
    /\ seedUsed' = newSeed
    /\ announced' = newAnnounced
    /\ signalsSent' = signalsSent

Step(i) ==
  IF i = Counter THEN CounterStep ELSE NonCounterStep(i)

Vars == << lampOn, count, signalsSent, visited, announced, seedUsed >>

Next ==
  \/ /\ ~announced
     /\ \E i \in Prisoners: Step(i)
  \/ /\ announced
     /\ UNCHANGED Vars

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in Prisoners: WF_Vars(Step(i))

\* Safety: any victory announcement implies every prisoner has visited the cell.
AllVisited == \A i \in Prisoners: visited[i]
SafetyInvariant == announced => AllVisited
SafetyAlways == [](SafetyInvariant)

\* Liveness: under weak fairness of the warden's selection, victory is eventually announced.
VictoryEventually == <>announced

=============================================================================