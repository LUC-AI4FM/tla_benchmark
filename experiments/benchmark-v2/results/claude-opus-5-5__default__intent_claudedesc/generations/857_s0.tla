---------------------------- MODULE PrisonerLamp ----------------------------
(***************************************************************************)
(* The prisoner lamp puzzle.                                               *)
(*                                                                         *)
(* A warden repeatedly picks any prisoner and puts them alone in a room    *)
(* that holds a single lamp. The lamp is either on or off. A prisoner may  *)
(* declare that every prisoner has visited the room at least once.         *)
(*                                                                         *)
(* Strategy: one designated prisoner, the Counter, keeps a count that      *)
(* starts at 1 to account for the Counter itself.                          *)
(*  - When the Counter finds the lamp on, it turns the lamp off and adds   *)
(*    1 to the count. It declares victory when the count reaches the       *)
(*    Threshold.                                                           *)
(*  - When any other prisoner finds the lamp off, it turns the lamp on,    *)
(*    as long as it has signalled fewer than MaxSignals times.             *)
(*                                                                         *)
(* The variants:                                                           *)
(*   LampKnownOff = TRUE : MaxSignals = 1, Threshold = N                   *)
(*   LampKnownOff = FALSE: MaxSignals = 2, Threshold = 2N - 1              *)
(*                                                                         *)
(* In the unknown variant the lamp may start on, which gives at most one   *)
(* spurious signal. So the Counter must see 2N - 2 signals before it       *)
(* declares. Count = 1 + signals, so the declaration happens at 2N - 1.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,       \* the set of prisoners
          Counter,        \* the designated counting prisoner
          LampKnownOff    \* TRUE iff the lamp is known to start off

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Prisoner # {}
       /\ Counter \in Prisoner
       /\ LampKnownOff \in BOOLEAN

N == Cardinality(Prisoner)

Others == Prisoner \ {Counter}

MaxSignals == IF LampKnownOff THEN 1 ELSE 2

Threshold == IF LampKnownOff THEN N ELSE 2 * N - 1

VARIABLES lamp,      \* "on" or "off"
          signals,   \* signals[p]: how many times non-counter p turned the lamp on
          count,     \* the Counter's count (includes the Counter itself)
          declared,  \* TRUE once the Counter has announced victory
          visited    \* ghost variable: the set of prisoners who have visited the room

vars == <<lamp, signals, count, declared, visited>>

TypeOK ==
  /\ lamp \in {"on", "off"}
  /\ signals \in [Others -> 0..MaxSignals]
  /\ count \in 1..(Threshold + 1)
  /\ declared \in BOOLEAN
  /\ visited \subseteq Prisoner

Init ==
  /\ lamp \in (IF LampKnownOff THEN {"off"} ELSE {"on", "off"})
  /\ signals = [p \in Others |-> 0]
  /\ count = 1
  /\ declared = FALSE
  /\ visited = {}

CounterStep ==
  LET newCount == IF lamp = "on" THEN count + 1 ELSE count
  IN  /\ lamp' = "off"
      /\ count' = newCount
      /\ declared' = (newCount >= Threshold)
      /\ UNCHANGED signals

OtherStep(p) ==
  /\ IF lamp = "off" /\ signals[p] < MaxSignals
        THEN /\ lamp' = "on"
             /\ signals' = [signals EXCEPT ![p] = @ + 1]
        ELSE UNCHANGED <<lamp, signals>>
  /\ UNCHANGED <<count, declared>>

\* The warden selects prisoner p and places them in the room.
Visit(p) ==
  /\ ~declared
  /\ visited' = visited \cup {p}
  /\ IF p = Counter THEN CounterStep ELSE OtherStep(p)

\* Once victory is declared the game is over. This step avoids deadlock.
Done ==
  /\ declared
  /\ UNCHANGED vars

Next == (\E p \in Prisoner : Visit(p)) \/ Done

\* Warden fairness: each prisoner is eventually selected again and again.
Fairness == \A p \in Prisoner : WF_vars(Visit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* Safety: victory is declared only if every prisoner has truly visited.
Safety == declared => (visited = Prisoner)

\* Auxiliary invariant: the count never exceeds what the signals can explain.
CountBound ==
  LET RECURSIVE SumOver(_)
      SumOver(S) == IF S = {} THEN 0
                    ELSE LET q == CHOOSE q \in S : TRUE
                         IN  signals[q] + SumOver(S \ {q})
  IN  count - 1 <= SumOver(Others) + (IF LampKnownOff THEN 0 ELSE 1)

\* Liveness: the prisoners eventually win.
Liveness == <>declared

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================