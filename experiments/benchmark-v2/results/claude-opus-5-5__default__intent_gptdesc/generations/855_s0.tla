------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner,   \* the set of all prisoners
          Counter     \* the designated counting prisoner

ASSUME /\ IsFiniteSet(Prisoner)
       /\ Cardinality(Prisoner) > 1
       /\ Counter \in Prisoner

OtherPrisoner == Prisoner \ {Counter}

(***************************************************************************)
(* Threshold at which the counter declares.  Every non-counter prisoner   *)
(* contributes at most 2 "ups" of switch A.  Because switch A may start   *)
(* up, the counter may receive one spurious unit.  If some non-counter    *)
(* prisoner had never visited, the count could be at most                *)
(* 2*(N-2) + 1 = 2*(N-1) - 1.  So reaching 2*(N-1) guarantees everyone    *)
(* has visited.                                                           *)
(***************************************************************************)
Threshold == 2 * Cardinality(OtherPrisoner)

VARIABLES
  switchAUp,      \* position of switch A (the signalling switch)
  switchBUp,      \* position of switch B (the dummy switch)
  timesSwitched,  \* for each non-counter prisoner, how often she raised A
  count,          \* the counter's internal tally
  declared,       \* TRUE once the counter has announced "all have visited"
  visited         \* ghost: set of prisoners who have entered the room

vars == <<switchAUp, switchBUp, timesSwitched, count, declared, visited>>

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count \in 0..(Threshold + 1)
  /\ declared \in BOOLEAN
  /\ visited \subseteq Prisoner

(***************************************************************************)
(* Sum of a function's values over a finite set.                          *)
(***************************************************************************)
RECURSIVE SetSum(_, _)
SetSum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SetSum(f, S \ {x})

TotalContributions == SetSum(timesSwitched, OtherPrisoner)

(***************************************************************************)
(* Initial state: the switch positions are unknown (arbitrary).           *)
(***************************************************************************)
Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count = 0
  /\ declared = FALSE
  /\ visited = {}

(***************************************************************************)
(* Strategy of a non-counter prisoner: if switch A is down and she has    *)
(* raised it fewer than twice, she sets A up; otherwise she flips B.      *)
(* Each step performs exactly one atomic change of one switch.            *)
(***************************************************************************)
NonCounterStep(i) ==
  /\ visited' = visited \cup {i}
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @ + 1]
            /\ UNCHANGED <<switchBUp, count, declared>>
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched, count, declared>>

(***************************************************************************)
(* Strategy of the counter: if switch A is up, she sets it down and       *)
(* increments her tally, declaring once the tally reaches Threshold;      *)
(* otherwise she flips B.                                                  *)
(***************************************************************************)
CounterStep ==
  /\ visited' = visited \cup {Counter}
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ count' = count + 1
            /\ declared' = (declared \/ (count + 1 >= Threshold))
            /\ UNCHANGED <<switchBUp, timesSwitched>>
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched, count, declared>>

(***************************************************************************)
(* A single prisoner, chosen arbitrarily, enters the room.                *)
(***************************************************************************)
Step(i) == IF i = Counter THEN CounterStep ELSE NonCounterStep(i)

Next == \E i \in Prisoner : Step(i)

(***************************************************************************)
(* Fairness: no prisoner is starved; each is chosen infinitely often.     *)
(* Step(i) is always enabled, so weak fairness forces infinitely many     *)
(* Step(i) steps for every i.                                             *)
(***************************************************************************)
Fairness == \A i \in Prisoner : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Allowed kind of state update: every non-stuttering step changes        *)
(* exactly one switch.                                                     *)
(***************************************************************************)
ExactlyOneSwitchChange ==
  [][ (switchAUp' /= switchAUp) /= (switchBUp' /= switchBUp) ]_vars

(***************************************************************************)
(* Safety: a declaration is made only when every prisoner (including the  *)
(* counter) has visited the room.                                          *)
(***************************************************************************)
Safety == declared => (visited = Prisoner)

(***************************************************************************)
(* Key inductive invariants used to prove safety.                         *)
(***************************************************************************)

\* Accounting relation: the counter's tally plus a pending "up" of switch A
\* equals the total contributions of non-counter prisoners, plus at most one
\* spurious unit caused by the unknown initial position of switch A.
CountInvariant ==
  (count + (IF switchAUp THEN 1 ELSE 0)) \in {TotalContributions, TotalContributions + 1}

\* Only prisoners that have visited have contributed.
ContributorsVisited ==
  \A i \in OtherPrisoner : timesSwitched[i] > 0 => i \in visited

\* The counter has visited whenever she has counted anything.
CounterVisited == count > 0 => Counter \in visited

\* Declaration only happens at or above the threshold.
DeclaredImpliesThreshold == declared => count >= Threshold

Inv ==
  /\ TypeOK
  /\ CountInvariant
  /\ ContributorsVisited
  /\ CounterVisited
  /\ DeclaredImpliesThreshold
  /\ Safety

THEOREM Spec => []Inv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: under fairness, the counter eventually declares.             *)
(***************************************************************************)
Liveness == <>declared

\* Once declared, the declaration is never retracted.
DeclarationStable == [](declared => []declared)

THEOREM Spec => Liveness
=============================================================================