--------------------------- MODULE OneStepByzantineConsensus ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T
ASSUME N > 3 * T && T >= 0

VARIABLES proposals, messages, decisions, correctCounters, faultyCounters, undecided

TypeOK == 
  /\ proposals \in [1..N -> {0, 1}]
  /\ messages \in [1..N -> Nat -> {0, 1}]
  /\ decisions \in [1..N -> {0, 1, <<>>}]
  /\ correctCounters \in [1..N -> Nat]
  /\ faultyCounters \in [1..N -> Nat]
  /\ undecided \in [1..N -> Boolean]

OneStep0_Ltl == 
  <>[]<>(\E p \in (1..N) : decisions[p] = 0)

OneStep1_Ltl == 
  []<>(\A p \in (1..N) : decisions[p] = 1)

AllDecideOne == 
  <>[](\A p \in (1..N) : decisions[p] = 1)

Spec == 
  /\ TypeOK
  /\ proposals = [p \in 1..N |-> IF p <= N - T THEN 0 ELSE 1]
  /\ messages = [p \in 1..N |-> [q \in Nat |-> 0]]
  /\ decisions = [p \in 1..N |-> <<>>]
  /\ correctCounters = [p \in 1..N |-> 0]
  /\ faultyCounters = [p \in 1..N |-> 0]
  /\ undecided = [p \in 1..N |-> TRUE]
  /\ WF_(vars)(CorrectPropose)
  /\ SF_(vars)(CorrectDecide)

CorrectPropose == 
  \E p \in (1..N) : 
    /\ correctCounters[p] < N - T
    /\ proposals[p] = 0
    /\ messages' = [messages EXCEPT ![p][correctCounters[p] + 1] = 0]
    /\ correctCounters' = [correctCounters EXCEPT ![p] = @ + 1]
    /\ undecided' = [undecided EXCEPT ![p] = FALSE]

CorrectDecide == 
  \E p \in (1..N) : 
    /\ undecided[p]
    /\ (\E v \in {0, 1} : 
        /\ messages[p][v] >= N - T
        /\ decisions' = [decisions EXCEPT ![p] = v]
      )
    \/ 
    /\ messages[p][0] < N - T
    /\ messages[p][1] < N - T
    /\ decisions' = [decisions EXCEPT ![p] = proposals[p]]

vars == <<proposals, messages, decisions, correctCounters, faultyCounters, undecided>>
=============================================================================