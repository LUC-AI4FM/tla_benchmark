------------------------------ MODULE Prisoners ------------------------------
(***************************************************************************)
(* The "prisoners and switches" puzzle.                                    *)
(*                                                                         *)
(* N > 1 prisoners, one of whom is the designated Counter.  At each step   *)
(* one prisoner, chosen fairly, enters a room with two binary switches A   *)
(* and B.  She must perform exactly one atomic change: flip one switch or  *)
(* set a switch to a given position.  The initial switch positions are     *)
(* unknown.                                                                *)
(*                                                                         *)
(* Strategy:                                                               *)
(*  - A non-counter prisoner who finds switch A down and has turned it up  *)
(*    fewer than 2 times turns A up.  Otherwise she flips switch B.        *)
(*  - The Counter, finding switch A up, turns it down and increments her   *)
(*    tally.  Otherwise she flips switch B.                                *)
(*  - The Counter declares that everyone has visited when her tally        *)
(*    reaches 2*(N-1).                                                     *)
(*                                                                         *)
(* Each non-counter turns A up at most twice.  Switch A may have started   *)
(* up, which adds at most one extra count.  If some non-counter never      *)
(* visited, the tally is at most 2*(N-2) + 1 = 2N - 3.  That is less than  *)
(* 2N - 2, so the declaration is never mistaken.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Counter \in Prisoner
       /\ Cardinality(Prisoner) > 1

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp,      \* position of switch A
          switchBUp,      \* position of switch B
          timesSwitched,  \* times each non-counter has turned A up
          count,          \* the Counter's internal tally
          visited         \* ghost: the set of prisoners who have entered

vars == <<switchAUp, switchBUp, timesSwitched, count, visited>>

N == Cardinality(Prisoner)

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(2 * N - 1)
  /\ visited \subseteq Prisoner

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0
  /\ visited = {}

(* The terminal signaling condition: the Counter declares. *)
Done == count >= 2 * (N - 1)

NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ visited' = visited \cup {i}
  /\ UNCHANGED count

CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ visited' = visited \cup {Counter}
  /\ UNCHANGED timesSwitched

Next == CounterStep \/ \E i \in OtherPrisoner : NonCounterStep(i)

(* No prisoner is starved. *)
Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Sum of the values of a function over a finite set of its domain. *)
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SumOver(f, S \ {x})

(***************************************************************************)
(* Accounting invariant.  The total number of times non-counters have      *)
(* turned A up, plus the possible initial "up" of switch A, equals the     *)
(* Counter's tally plus whether A is currently up.                         *)
(***************************************************************************)
CountInvariant ==
  LET totalSwitched == SumOver(timesSwitched, OtherPrisoner)
      oneIfUp       == IF switchAUp THEN 1 ELSE 0
  IN  /\ totalSwitched <= count + oneIfUp
      /\ count + oneIfUp <= totalSwitched + 1
      /\ \A i \in OtherPrisoner : (timesSwitched[i] > 0) => (i \in visited)
      /\ (count > 0) => (Counter \in visited)

(* A declaration is made only when every prisoner has visited. *)
Safety == Done => (visited = Prisoner)

(* Eventually the Counter can declare. *)
Liveness == <>Done

THEOREM Spec => [](TypeOK /\ CountInvariant /\ Safety)
THEOREM Spec => Liveness
=============================================================================