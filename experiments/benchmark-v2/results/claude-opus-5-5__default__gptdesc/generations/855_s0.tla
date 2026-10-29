------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME
  /\ IsFiniteSet(Prisoner)
  /\ Counter \in Prisoner
  /\ Cardinality(Prisoner) > 1

OtherPrisoner == Prisoner \ {Counter}

(* Each non-counter prisoner raises switch A at most twice.  The initial    *)
(* position of switch A is unknown, so the counter may see one extra       *)
(* "up".  He declares completion when count reaches 2*(N-1).               *)
TotalCount == 2 * (Cardinality(Prisoner) - 1)

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(TotalCount + 1)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0

(* The counter enters the room. *)
CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched

(* A non-counter prisoner i enters the room. *)
OtherStep(i) ==
  /\ IF ~switchAUp /\ timesSwitched[i] < 2
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : OtherStep(i)

Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(OtherStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Done == count >= TotalCount

(* Safety: when the counter declares completion, every prisoner has been   *)
(* in the room (the counter has visited since count > 0, and every other   *)
(* prisoner has raised switch A at least once).                            *)
Safety ==
  Done => /\ count > 0
          /\ \A i \in OtherPrisoner : timesSwitched[i] > 0

(* Liveness: the declaration condition is eventually reached. *)
Liveness == <>Done

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================