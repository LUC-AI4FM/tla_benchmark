------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,      \* the set of all prisoners
          Counter,       \* the designated counter prisoner
          LightUnknown   \* TRUE: initial lamp state unknown; FALSE: initially off

ASSUME /\ Counter \in Prisoner
       /\ IsFiniteSet(Prisoner)
       /\ LightUnknown \in BOOLEAN

OtherPrisoner == Prisoner \ {Counter}

N == Cardinality(Prisoner)

\* Number of times each non-counter prisoner may turn the lamp on.
MaxSignals == IF LightUnknown THEN 2 ELSE 1

\* The counter starts its tally at 1, counting itself. It announces when
\* the tally reaches Threshold.
Threshold == IF LightUnknown THEN 2 * N - 1 ELSE N

VARIABLES light,      \* state of the lamp in the special cell: "on" or "off"
          count,      \* the counter's tally
          signalled,  \* signalled[p]: times non-counter p has turned the lamp on
          visited,    \* visited[p]: TRUE iff p has been in the cell
          announced   \* TRUE iff the counter has announced victory

vars == <<light, count, signalled, visited, announced>>

TypeOK ==
  /\ light \in {"on", "off"}
  /\ count \in 0..Threshold
  /\ signalled \in [OtherPrisoner -> 0..MaxSignals]
  /\ visited \in [Prisoner -> BOOLEAN]
  /\ announced \in BOOLEAN

Init ==
  /\ light \in IF LightUnknown THEN {"on", "off"} ELSE {"off"}
  /\ count = 1
  /\ signalled = [p \in OtherPrisoner |-> 0]
  /\ visited = [p \in Prisoner |-> FALSE]
  /\ announced = FALSE

(***************************************************************************)
(* A non-counter prisoner who finds the lamp off and has not yet used all  *)
(* of its signals turns the lamp on.                                       *)
(***************************************************************************)
Signal(p) ==
  /\ ~announced
  /\ light = "off"
  /\ signalled[p] < MaxSignals
  /\ light' = "on"
  /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<count, announced>>

(***************************************************************************)
(* The counter, finding the lamp on, turns it off and increments its       *)
(* tally. When the tally reaches the threshold, it announces victory.      *)
(***************************************************************************)
CounterStep ==
  /\ ~announced
  /\ light = "on"
  /\ light' = "off"
  /\ count' = count + 1
  /\ announced' = (count + 1 = Threshold)
  /\ visited' = [visited EXCEPT ![Counter] = TRUE]
  /\ UNCHANGED signalled

(***************************************************************************)
(* A prisoner visits the cell and leaves the lamp unchanged.               *)
(***************************************************************************)
IdleVisit(p) ==
  /\ ~announced
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<light, count, signalled, announced>>

Next ==
  \/ \E p \in OtherPrisoner : Signal(p)
  \/ CounterStep
  \/ \E p \in Prisoner : IdleVisit(p)

Fairness ==
  /\ \A p \in OtherPrisoner : WF_vars(Signal(p))
  /\ WF_vars(CounterStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: any victory announcement implies every prisoner has visited.    *)
Safety == announced => \A p \in Prisoner : visited[p]

(* Liveness: the prisoners eventually announce victory.                    *)
Liveness == <>announced

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================