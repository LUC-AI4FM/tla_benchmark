------------------------------ MODULE PrisonerLamp ------------------------------

EXTENDS Naturals

CONSTANTS N, Counter, KnownOff

ASSUME N \in Nat /\ N >= 1
ASSUME Counter \in 1..N

(*
  P is the set of prisoners; Counter \in P is the designated counter.
*)
P == 1..N

(*
  Threshold per variant:
  - Known-off: declare at count = N (counter starts from 1)
  - Unknown:   declare at count = 2N - 1 (counter starts from 0)
*)
THRESHOLD == IF KnownOff THEN N ELSE 2*N - 1

VARIABLES
  lamp,         \* lamp state: TRUE = on, FALSE = off
  count,        \* counter's count of "offs" performed when finding lamp on
  visited,      \* [P -> BOOLEAN], whether each prisoner has visited at least once
  signalsLeft,  \* [P -> Nat], remaining times a non-counter may flip off->on
  primed,       \* whether the counter has performed the one-time priming (unknown variant)
  won           \* whether victory has been declared

vars == << lamp, count, visited, signalsLeft, primed, won >>

TypeInv ==
  /\ lamp \in {TRUE, FALSE}
  /\ count \in Nat
  /\ visited \in [P -> BOOLEAN]
  /\ signalsLeft \in [P -> Nat]
  /\ primed \in {TRUE, FALSE}
  /\ won \in {TRUE, FALSE}

Init ==
  /\ (KnownOff => lamp = FALSE)
  /\ (~KnownOff => lamp \in {TRUE, FALSE})
  /\ count = IF KnownOff THEN 1 ELSE 0
  /\ visited = [ i \in P |-> FALSE ]
  /\ signalsLeft =
       [ i \in P |-> IF i = Counter THEN 0 ELSE IF KnownOff THEN 1 ELSE 2 ]
  /\ primed = IF KnownOff THEN TRUE ELSE FALSE
  /\ won = FALSE
  /\ TypeInv

(*
  Non-counter i's move when selected by the warden.
  Strategy: if lamp is off and i has remaining signals, turn it on (consume one).
*)
NonCounterMove(i) ==
  /\ i \in P /\ i # Counter
  /\ IF (~lamp /\ signalsLeft[i] > 0) THEN
        /\ lamp' = TRUE
        /\ signalsLeft' = [signalsLeft EXCEPT ![i] = @ - 1]
     ELSE
        /\ UNCHANGED << lamp, signalsLeft >>
  /\ UNCHANGED << count, primed, won >>

(*
  Counter's move when selected by the warden.
  Priority:
    1) If threshold reached, declare victory.
    2) Else if lamp is on, turn it off and increment count.
    3) Else if unknown variant and not yet primed, and lamp is off, prime by turning it on once.
    4) Else do nothing.
*)
CounterMove ==
  /\ IF count >= THRESHOLD THEN
        /\ won' = TRUE
        /\ UNCHANGED << lamp, signalsLeft, count, primed >>
     ELSE IF lamp THEN
        /\ lamp' = FALSE
        /\ count' = count + 1
        /\ UNCHANGED << signalsLeft, primed, won >>
     ELSE IF ~KnownOff /\ ~primed /\ ~lamp THEN
        /\ lamp' = TRUE
        /\ primed' = TRUE
        /\ UNCHANGED << signalsLeft, count, won >>
     ELSE
        /\ UNCHANGED << lamp, signalsLeft, count, primed, won >>

(*
  A single warden selection: choose prisoner i to visit the cell.
*)
Visit(i) ==
  /\ ~won
  /\ i \in P
  /\ visited' = [visited EXCEPT ![i] = TRUE]
  /\ IF i = Counter THEN CounterMove ELSE NonCounterMove(i)

(*
  System steps: either a warden selection occurs, or stuttering.
*)
Next ==
  \/ \E i \in P: Visit(i)
  \/ UNCHANGED vars

(*
  Fairness: the warden is strongly fair in selecting each prisoner.
  Since Visit(i) is enabled whenever ~won, SF ensures each i is selected infinitely often until victory.
*)
Fairness == \A i \in P: SF_vars(Visit(i))

(*
  Safety: victory is never declared unless every prisoner has visited at least once.
*)
AllVisited == \A i \in P: visited[i]
Safety == [](won => AllVisited)

(*
  Liveness: the prisoners eventually win.
*)
Liveness == <>won

Spec == Init /\ [][Next]_vars /\ Fairness

===============================================================================