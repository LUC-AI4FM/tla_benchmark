------------------------------- MODULE PrisonersLightSwitch -------------------------------

EXTENDS Naturals

CONSTANTS N, Counter, KnownOff

ASSUME N \in Nat /\ N >= 1
ASSUME Counter \in 1..N
ASSUME KnownOff \in BOOLEAN

P == 1..N

MaxSignals == IF KnownOff THEN 1 ELSE 2

Threshold == IF KnownOff THEN (N - 1) ELSE (2*N - 1)

VARIABLES lamp, signals, count, announced, visited

vars == << lamp, signals, count, announced, visited >>

Init ==
  /\ lamp \in BOOLEAN
  /\ KnownOff => lamp = FALSE
  /\ signals = [p \in P |-> 0]
  /\ count = 0
  /\ announced = FALSE
  /\ visited = [p \in P |-> FALSE]

Step(p) ==
  /\ p \in P
  /\ ~announced
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ IF p = Counter
        THEN
          /\ LET inc == IF lamp THEN 1 ELSE 0 IN
               /\ count' = count + inc
               /\ lamp' = IF lamp THEN FALSE ELSE lamp
               /\ announced' = announced \/ (count + inc >= Threshold)
          /\ signals' = signals
        ELSE
          /\ count' = count
          /\ announced' = announced
          /\ IF (~lamp) /\ (signals[p] < MaxSignals)
                THEN
                  /\ lamp' = TRUE
                  /\ signals' = [signals EXCEPT ![p] = @ + 1]
                ELSE
                  /\ lamp' = lamp
                  /\ signals' = signals

Next == \E p \in P: Step(p)

Spec == Init /\ [][Next]_vars /\ (\A p \in P: WF_vars(Step(p)))

TypeInv ==
  /\ lamp \in BOOLEAN
  /\ signals \in [P -> Nat]
  /\ count \in Nat
  /\ announced \in BOOLEAN
  /\ visited \in [P -> BOOLEAN]
  /\ signals[Counter] = 0

VisitedAll == \A p \in P: visited[p]

Victory == announced

Safety == announced => VisitedAll

SafetyAlways == []Safety

EventuallyVictory == <>Victory

==========================================================================================