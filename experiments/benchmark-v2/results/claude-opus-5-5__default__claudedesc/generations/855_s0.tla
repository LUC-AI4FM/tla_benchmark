---------------------------- MODULE Prisoners -----------------------------
(***************************************************************************)
(* A solution to the "Prisoners and Switches" puzzle.                      *)
(*                                                                         *)
(* A warden repeatedly picks a prisoner to enter a room with two switches, *)
(* A and B. Each visiting prisoner must flip exactly one switch. A single  *)
(* designated prisoner, Counter, uses switch A to count. Every other       *)
(* prisoner raises switch A at most twice, and only when it is down.       *)
(* Otherwise that prisoner toggles switch B. The Counter lowers switch A   *)
(* whenever it is up and adds one to its count. Otherwise it toggles       *)
(* switch B. When count reaches 2 * (Cardinality(Prisoner) - 1), the       *)
(* Counter declares that every prisoner has visited the room.              *)
(*                                                                         *)
(* The switches may start in any position, which is why each non-counter   *)
(* prisoner must raise switch A twice.                                     *)
(*                                                                         *)
(* The model is checked with four prisoners for TypeOK, CountInvariant,    *)
(* Safety and Liveness.                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Counter \in Prisoner
       /\ Prisoner \ {Counter} # {}

OtherPrisoner == Prisoner \ {Counter}

VARIABLES switchAUp, switchBUp, timesSwitched, count

vars == <<switchAUp, switchBUp, timesSwitched, count>>

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0 .. (2 * Cardinality(Prisoner) - 1)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0

(***************************************************************************)
(* Action of a non-counter prisoner i during a visit to the room.          *)
(***************************************************************************)
NonCounterStep(i) ==
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count

(***************************************************************************)
(* Action of the Counter during a visit to the room.                       *)
(***************************************************************************)
CounterStep ==
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ UNCHANGED switchBUp
            /\ count' = count + 1
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched

Next ==
  \/ CounterStep
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

(***************************************************************************)
(* The warden guarantees that every prisoner visits the room infinitely    *)
(* often. This is expressed as weak fairness of each prisoner's action.    *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
Done == count = 2 * (Cardinality(Prisoner) - 1)

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE
                 IN  f[x] + SumOver(f, S \ {x})

(***************************************************************************)
(* Every upward flip of switch A was made by a non-counter prisoner, and   *)
(* switch A may also have started in the up position. Each downward flip   *)
(* adds one to count. So count + (1 if A is up) equals the total number    *)
(* of upward flips plus 0 or 1, depending on A's initial position.         *)
(***************************************************************************)
CountInvariant ==
  LET totalSwitched == SumOver(timesSwitched, OtherPrisoner)
      oneIfUp       == IF switchAUp THEN 1 ELSE 0
  IN  count + oneIfUp \in {totalSwitched, totalSwitched + 1}

Safety ==
  [](Done => (\A i \in OtherPrisoner : timesSwitched[i] > 0))

Liveness == <>Done

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []CountInvariant
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================