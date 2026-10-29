------------------------------ MODULE PrisonerLightSwitch ------------------------------
(***************************************************************************)
(* The prisoner light-switch puzzle with one designated counter prisoner  *)
(* and a single shared lamp in a special cell.                             *)
(*                                                                         *)
(* The warden repeatedly picks a prisoner and sends them to the cell.      *)
(* While there, the prisoner may toggle the lamp.  The counter may at any  *)
(* time announce that every prisoner has visited the cell.                 *)
(*                                                                         *)
(* Two variants are modeled, selected by the constant LightUnknown:        *)
(*  - LightUnknown = FALSE: the lamp is known to start off.  Each          *)
(*    non-counter prisoner signals once, and the counter waits for a       *)
(*    threshold of N.                                                      *)
(*  - LightUnknown = TRUE: the initial lamp state is unknown.  Each         *)
(*    non-counter prisoner signals twice, and the counter waits for a      *)
(*    threshold of 2N - 1.                                                 *)
(*                                                                         *)
(* N is the total number of prisoners.  The counter's tally starts at 1,   *)
(* which accounts for the counter itself.                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Prisoner,       \* the set of all prisoners
    Counter,        \* the designated counter prisoner
    LightUnknown    \* TRUE iff the initial lamp state is unknown

ASSUME PrisonerAssump == IsFiniteSet(Prisoner) /\ Prisoner # {}
ASSUME CounterAssump  == Counter \in Prisoner
ASSUME UnknownAssump  == LightUnknown \in BOOLEAN

N == Cardinality(Prisoner)

OtherPrisoner == Prisoner \ {Counter}

\* Number of times each non-counter prisoner turns the lamp on
MaxSignals == IF LightUnknown THEN 2 ELSE 1

\* Tally the counter must reach before announcing
Threshold == IF LightUnknown THEN 2 * N - 1 ELSE N

VARIABLES
    lightOn,    \* state of the lamp in the special cell
    count,      \* the counter's tally (including the counter itself)
    signalled,  \* signalled[p]: times non-counter p has turned the lamp on
    visited,    \* set of prisoners who have actually visited the cell
    announced   \* TRUE once the counter has announced victory

vars == << lightOn, count, signalled, visited, announced >>

TypeOK ==
    /\ lightOn \in BOOLEAN
    /\ count \in Nat
    /\ signalled \in [OtherPrisoner -> 0..MaxSignals]
    /\ visited \subseteq Prisoner
    /\ announced \in BOOLEAN

Init ==
    /\ lightOn \in (IF LightUnknown THEN BOOLEAN ELSE {FALSE})
    /\ count = 1
    /\ signalled = [p \in OtherPrisoner |-> 0]
    /\ visited = {}
    /\ announced = FALSE

\* A non-counter prisoner visits the cell
OtherVisit(p) ==
    /\ p \in OtherPrisoner
    /\ visited' = visited \cup {p}
    /\ IF ~lightOn /\ signalled[p] < MaxSignals
         THEN /\ lightOn' = TRUE
              /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
         ELSE UNCHANGED << lightOn, signalled >>
    /\ UNCHANGED << count, announced >>

\* The counter visits the cell
CounterVisit ==
    /\ visited' = visited \cup {Counter}
    /\ IF lightOn
         THEN /\ lightOn' = FALSE
              /\ count' = count + 1
         ELSE UNCHANGED << lightOn, count >>
    /\ announced' = (count' >= Threshold)
    /\ UNCHANGED signalled

\* The warden sends prisoner p to the cell
Enter(p) ==
    /\ ~announced
    /\ IF p = Counter THEN CounterVisit ELSE OtherVisit(p)

\* After the announcement the game is over
Done ==
    /\ announced
    /\ UNCHANGED vars

Next == (\E p \in Prisoner : Enter(p)) \/ Done

\* Weak fairness of the warden's selection: every prisoner keeps being chosen
Fairness == \A p \in Prisoner : WF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------
(* Safety: a victory announcement implies every prisoner has visited the cell *)
Safety == announced => (visited = Prisoner)

(* Liveness: the prisoners eventually announce victory *)
Liveness == <>announced

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=======================================================================================