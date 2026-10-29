--------------------------- MODULE PrisonerLightSwitch ---------------------------
(***************************************************************************)
(* The prisoner light-switch puzzle with a designated counter prisoner     *)
(* and a single shared lamp in a special cell.                             *)
(*                                                                         *)
(* Standard variant (LightUnknown = FALSE): the lamp starts off. Each      *)
(* non-counter prisoner turns the lamp on exactly once, the first time     *)
(* they find it off. The counter turns the lamp off whenever they find it  *)
(* on, and counts each time. The counter's count starts at 1 to include    *)
(* the counter. The counter announces when the count reaches N, where N    *)
(* is the total number of prisoners.                                       *)
(*                                                                         *)
(* Harder variant (LightUnknown = TRUE): the initial lamp state is         *)
(* unknown. Each non-counter prisoner may signal twice, and the counter    *)
(* waits for a threshold of 2N - 1. That threshold can be reached without  *)
(* the initial lamp: 1 + 2(N-1) = 2N - 1. If the lamp was initially on,    *)
(* one count may be spurious. Even so, reaching 2N - 1 implies at least    *)
(* 2N - 3 real signals from N - 1 prisoners, so every prisoner signalled   *)
(* at least once.                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,      \* the set of all prisoners
          Counter,       \* the designated counter prisoner
          LightUnknown   \* TRUE iff the initial lamp state is unknown

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Counter \in Prisoner
       /\ LightUnknown \in BOOLEAN

OtherPrisoner == Prisoner \ {Counter}

N == Cardinality(Prisoner)

MaxSignals == IF LightUnknown THEN 2 ELSE 1

Threshold == IF LightUnknown THEN 2 * N - 1 ELSE N

VARIABLES lightOn,    \* state of the lamp in the special cell
          count,      \* the counter's tally (includes the counter himself)
          signals,    \* signals[p] = number of times p has turned the lamp on
          visited,    \* visited[p] = TRUE iff p has actually been in the cell
          announced   \* TRUE iff the counter has announced victory

vars == <<lightOn, count, signals, visited, announced>>

TypeOK ==
  /\ lightOn \in BOOLEAN
  /\ count \in 1..(Threshold + 1)
  /\ signals \in [OtherPrisoner -> 0..MaxSignals]
  /\ visited \in [Prisoner -> BOOLEAN]
  /\ announced \in BOOLEAN

Init ==
  /\ lightOn \in (IF LightUnknown THEN BOOLEAN ELSE {FALSE})
  /\ count = 1
  /\ signals = [p \in OtherPrisoner |-> 0]
  /\ visited = [p \in Prisoner |-> FALSE]
  /\ announced = FALSE

(* The counter is brought to the cell. *)
CounterEnters ==
  /\ ~announced
  /\ visited' = [visited EXCEPT ![Counter] = TRUE]
  /\ IF lightOn
       THEN /\ lightOn' = FALSE
            /\ count' = count + 1
            /\ announced' = (count + 1 >= Threshold)
       ELSE UNCHANGED <<lightOn, count, announced>>
  /\ UNCHANGED signals

(* A non-counter prisoner p is brought to the cell. *)
OtherEnters(p) ==
  /\ ~announced
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ IF ~lightOn /\ signals[p] < MaxSignals
       THEN /\ lightOn' = TRUE
            /\ signals' = [signals EXCEPT ![p] = signals[p] + 1]
       ELSE UNCHANGED <<lightOn, signals>>
  /\ UNCHANGED <<count, announced>>

(* The warden selects a prisoner to enter the cell. *)
Enter(p) == IF p = Counter THEN CounterEnters ELSE OtherEnters(p)

(* After the announcement the system halts. This stuttering step avoids a deadlock. *)
Done == announced /\ UNCHANGED vars

Next == (\E p \in Prisoner : Enter(p)) \/ Done

(* Weak fairness of the warden's prisoner selection. *)
Fairness == \A p \in Prisoner : WF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: any victory announcement implies every prisoner has visited the cell. *)
Safety == announced => \A p \in Prisoner : visited[p]

(* Liveness: the prisoners eventually announce victory. *)
Success == <>announced

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Success
=============================================================================