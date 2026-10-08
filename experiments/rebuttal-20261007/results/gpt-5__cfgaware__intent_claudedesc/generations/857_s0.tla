------------------------------ MODULE PrisonerLamp ------------------------------

EXTENDS Naturals

CONSTANTS
  N,
  KnownOff,
  Counter

ASSUME /\ N \in Nat /\ N >= 1
       /\ KnownOff \in BOOLEAN
       /\ Counter \in 1..N

Prisoners == 1..N

MaxSignals(p) == IF p = Counter THEN 0 ELSE IF KnownOff THEN 1 ELSE 2

Threshold == IF KnownOff THEN N ELSE 2*N - 1

VARIABLES
  lamp,        \* lamp is a boolean: TRUE = on, FALSE = off
  visited,     \* [Prisoners -> BOOLEAN], has this prisoner visited the special cell at least once
  sig,         \* [Prisoners -> 0..2], number of times a non-counter has signaled (turned lamp on)
  count,       \* counter's tally
  victory      \* TRUE iff a prisoner has announced victory

vars == << lamp, visited, sig, count, victory >>

Init ==
  /\ IF KnownOff THEN lamp = FALSE ELSE lamp \in BOOLEAN
  /\ visited = [p \in Prisoners |-> FALSE]
  /\ sig = [p \in Prisoners |-> 0]
  /\ count = IF KnownOff THEN 1 ELSE 0
  /\ victory = FALSE

TypeOK ==
  /\ N \in Nat /\ N >= 1
  /\ Counter \in Prisoners
  /\ lamp \in BOOLEAN
  /\ visited \in [Prisoners -> BOOLEAN]
  /\ sig \in [Prisoners -> 0..2]
  /\ \A p \in Prisoners: sig[p] <= MaxSignals(p)
  /\ count \in Nat
  /\ victory \in BOOLEAN

AllVisited == \A p \in Prisoners: visited[p]

(*
  A visit step by the designated counter:
  - Marks the counter as visited.
  - If the lamp is on, turns it off and increments the count.
  - May declare victory when the strategy threshold is reached,
    or whenever in fact all prisoners have visited (safety-preserving).
*)
CounterVisit(p) ==
  /\ ~victory
  /\ p \in Prisoners /\ p = Counter
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ LET wasOn == lamp IN
     /\ lamp'  = IF wasOn THEN FALSE ELSE lamp
     /\ count' = count + IF wasOn THEN 1 ELSE 0
  /\ sig' = sig
  /\ victory' = victory
               \/ (count' >= Threshold)
               \/ (\A q \in Prisoners: visited'[q])

(*
  A non-counter visit that does not signal (does not change the lamp).
*)
NonCounterVisitNoSignal(p) ==
  /\ ~victory
  /\ p \in Prisoners /\ p # Counter
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ UNCHANGED << lamp, sig, count, victory >>

(*
  A non-counter visit that signals:
  - Allowed only if the lamp is off and the prisoner has remaining signals.
  - Turns the lamp on and consumes one signal.
*)
NonCounterVisitSignal(p) ==
  /\ ~victory
  /\ p \in Prisoners /\ p # Counter
  /\ lamp = FALSE
  /\ sig[p] < MaxSignals(p)
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ lamp' = TRUE
  /\ sig' = [sig EXCEPT ![p] = @ + 1]
  /\ UNCHANGED << count, victory >>

Visit(p) ==
  (p = Counter /\ CounterVisit(p))
  \/ (p # Counter /\ (NonCounterVisitNoSignal(p) \/ NonCounterVisitSignal(p)))

Next ==
  \E p \in Prisoners: Visit(p)

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A p \in Prisoners: SF_vars(Visit(p))

VictoryOK == victory => AllVisited

Terminating == <> victory

=============================================================================