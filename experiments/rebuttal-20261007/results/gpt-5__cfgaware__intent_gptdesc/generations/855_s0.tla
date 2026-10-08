------------------------------ MODULE PrisonersSwitches ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Prisoner, \* Finite, nonempty set of prisoners (N > 1)
  p2, p3     \* Distinguished elements provided by the model config

ASSUME
  /\ p2 \in Prisoner
  /\ p3 \in Prisoner
  /\ Cardinality(Prisoner) > 1

(*
Deterministic two-switch protocol with a single designated counter.
We use p2 as the designated counter to avoid introducing extra constants.
*)

Counter == p2
Others  == Prisoner \ {Counter}
N       == Cardinality(Prisoner)

VARIABLES
  s1, s2,            \* Two independent binary switches
  Visited,           \* [Prisoner -> BOOLEAN], has a prisoner visited at least once
  Contributed,       \* [Prisoner -> BOOLEAN], has a non-counter made her unique contribution
  tally,             \* Counter’s internal tally of collected contributions
  Declared           \* Terminal signaling condition set by the counter

vars == << s1, s2, Visited, Contributed, tally, Declared >>

TypeOK ==
  /\ s1 \in BOOLEAN
  /\ s2 \in BOOLEAN
  /\ Visited \in [Prisoner -> BOOLEAN]
  /\ Contributed \in [Prisoner -> BOOLEAN]
  /\ tally \in Nat
  /\ Declared \in BOOLEAN

Init ==
  /\ s1 = FALSE
  /\ s2 = FALSE
  /\ Visited = [p \in Prisoner |-> FALSE]
  /\ Contributed = [p \in Prisoner |-> FALSE]
  /\ tally = 0
  /\ Declared = FALSE

IsCounter(p) == p = Counter

(*
Allowed atomic updates when prisoner p is chosen:
- Exactly one switch bit changes per step (either set a switch or flip one).
- Strategy:
  - A non-counter who has not yet contributed, and finds s1 = FALSE, must set s1 := TRUE once and mark Contributed[p] := TRUE.
  - Otherwise, a non-counter flips s2.
  - The counter, if s1 = TRUE, must set s1 := FALSE and increment tally.
  - Once tally = Cardinality(Others), the counter flips s2 and sets Declared := TRUE.
  - Otherwise, the counter flips s2.
All steps also mark Visited[p] := TRUE.
*)

NonCounterContrib(p) ==
  /\ ~IsCounter(p)
  /\ ~Contributed[p]
  /\ ~s1
  /\ s1' = TRUE
  /\ s2' = s2
  /\ Contributed' = [Contributed EXCEPT ![p] = TRUE]
  /\ UNCHANGED << tally, Declared >>
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]

NonCounterIdle(p) ==
  /\ ~IsCounter(p)
  /\ ~(~Contributed[p] /\ ~s1)  \* Idle only when contribution is not enabled
  /\ s1' = s1
  /\ s2' = ~s2
  /\ UNCHANGED << Contributed, tally, Declared >>
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]

CounterCollect(p) ==
  /\ IsCounter(p)
  /\ s1
  /\ tally < Cardinality(Others)
  /\ s1' = FALSE
  /\ s2' = s2
  /\ tally' = tally + 1
  /\ UNCHANGED << Contributed, Declared >>
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]

CounterDeclare(p) ==
  /\ IsCounter(p)
  /\ ~Declared
  /\ tally = Cardinality(Others)
  /\ s1' = s1
  /\ s2' = ~s2
  /\ UNCHANGED << Contributed, tally >>
  /\ Declared' = TRUE
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]

CounterIdle(p) ==
  /\ IsCounter(p)
  /\ ~( s1 \/ (~Declared /\ tally = Cardinality(Others)) )
  /\ s1' = s1
  /\ s2' = ~s2
  /\ UNCHANGED << Contributed, tally, Declared >>
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]

Step(p) ==
  NonCounterContrib(p)
  \/ NonCounterIdle(p)
  \/ CounterCollect(p)
  \/ CounterDeclare(p)
  \/ CounterIdle(p)

Next ==
  \E p \in Prisoner : Step(p)

(*
Key accounting invariant:
- The counter never "contributes."
- tally never exceeds the number of non-counters.
- At all times, tally + (1 if s1 is TRUE else 0) equals
  the number of non-counters who have set Contributed = TRUE.
This captures that each non-counter’s unique contribution is either
still "pending" on s1 (uncollected) or has been collected into tally.
*)
ContribCount == Cardinality({ q \in Others : Contributed[q] })

CountInvariant ==
  /\ Contributed[Counter] = FALSE
  /\ tally \leq Cardinality(Others)
  /\ tally + IF s1 THEN 1 ELSE 0 = ContribCount
  /\ \A q \in Others : Contributed[q] => Visited[q]

AllVisited == \A p \in Prisoner : Visited[p]

(*
Safety: A declaration (terminal signaling condition) can only occur when
every prisoner has indeed visited at least once.
*)
Safety == [](Declared => AllVisited)

(*
Liveness: Under the fairness that no prisoner is starved, the protocol
eventually reaches the terminal signaling condition.
*)
Liveness == <> Declared

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A p \in Prisoner : SF_vars(Step(p))

=============================================================================