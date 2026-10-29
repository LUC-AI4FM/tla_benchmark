------------------------------- MODULE Prisoners -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Counter \in Prisoner

OtherPrisoner == Prisoner \ {Counter}

(* Each non-counter turns switch A up at most twice. The initial state of     *)
(* switch A is unknown, so it may contribute one extra count. If some         *)
(* non-counter never acted, the counter can count at most 2*(N-2)+1 = 2N-3.   *)
(* Counting to 2*(N-1) therefore guarantees that every non-counter has acted. *)
Goal == 2 * Cardinality(OtherPrisoner)

VARIABLES
    switchAUp,      \* state of switch A (the designated counting switch)
    switchBUp,      \* state of switch B (the dummy switch)
    timesSwitched,  \* number of times each non-counter has turned switch A up
    count,          \* number of times the counter has turned switch A down
    declared        \* TRUE once the counter declares that everyone has visited

vars == <<switchAUp, switchBUp, timesSwitched, count, declared>>

TypeOK ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched \in [OtherPrisoner -> 0..2]
    /\ count \in 0..(Goal + 1)
    /\ declared \in BOOLEAN

Init ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched = [p \in OtherPrisoner |-> 0]
    /\ count = 0
    /\ declared = FALSE

(* The counter's strategy: if switch A is up, turn it down and increment the  *)
(* count; otherwise flip switch B. Declare once the count reaches Goal.       *)
CounterStep ==
    /\ IF switchAUp
         THEN /\ switchAUp' = FALSE
              /\ count' = count + 1
              /\ UNCHANGED switchBUp
         ELSE /\ switchBUp' = ~switchBUp
              /\ UNCHANGED <<switchAUp, count>>
    /\ declared' = (declared \/ count' >= Goal)
    /\ UNCHANGED timesSwitched

(* A non-counter's strategy: if switch A is down and it has turned it up      *)
(* fewer than two times, turn it up; otherwise flip switch B.                 *)
OtherStep(p) ==
    /\ IF ~switchAUp /\ timesSwitched[p] < 2
         THEN /\ switchAUp' = TRUE
              /\ timesSwitched' = [timesSwitched EXCEPT ![p] = @ + 1]
              /\ UNCHANGED switchBUp
         ELSE /\ switchBUp' = ~switchBUp
              /\ UNCHANGED <<switchAUp, timesSwitched>>
    /\ UNCHANGED <<count, declared>>

PrisonerStep(p) ==
    IF p = Counter THEN CounterStep ELSE OtherStep(p)

Next == \E p \in Prisoner : PrisonerStep(p)

(* Every prisoner is selected infinitely often. *)
Fairness == \A p \in Prisoner : WF_vars(PrisonerStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

Done == count >= Goal

(* Safety: whenever the counter declares, every non-counter has flipped      *)
(* switch A at least once.                                                   *)
Safety ==
    (declared \/ Done) => \A p \in OtherPrisoner : timesSwitched[p] > 0

(* Liveness: the counter eventually reaches the completion condition and the *)
(* prisoners are freed (and stay freed).                                     *)
Liveness == <>Done /\ <>[]declared

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================