------------------------------ MODULE PrisonersSwitches ------------------------------

EXTENDS Naturals, FiniteSets

(*
  Classic "Prisoners and Switches" puzzle with a designated Counter.
  The warden selects a prisoner repeatedly. Each visit flips exactly one switch.
  Non-counters raise A at most twice in total (only when A is down), otherwise toggle B.
  The Counter turns A down when it is up and increments count; otherwise toggles B.
  When count reaches 2 * (Cardinality(Prisoner) - 1), Done holds.
*)

CONSTANTS Counter, p2, p3, p4

VARIABLES
  switchAUp,     \* Boolean: Is switch A up?
  switchBUp,     \* Boolean: Is switch B up?
  timesSwitched, \* Function NonCounters -> {0,1,2}: upward flips of A by each non-counter
  count          \* Natural in 0..MaxCount: Counter's tally

(***********************
 * Basic definitions   *
 ***********************)

Prisoner == {Counter, p2, p3, p4}

NonCounters == Prisoner \ {Counter}

MaxCount == 2 * (Cardinality(Prisoner) - 1)

Done == count = MaxCount

vars == << switchAUp, switchBUp, timesSwitched, count >>

(***********************
 * Initialization      *
 ***********************)

Init ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [ p \in NonCounters |-> 0 ]
  /\ count = 0

(***********************
 * Helper: sum over a  *
 * finite set domain   *
 ***********************)

RECURSIVE SumOver(_,_)
SumOver(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN  f[x] + SumOver(S \ {x}, f)

TotalUps == SumOver(NonCounters, timesSwitched)

(***********************
 * Per-prisoner steps  *
 ***********************)

CounterAct ==
  IF /\ switchAUp
     /\ count < MaxCount
  THEN /\ switchAUp' = FALSE
       /\ switchBUp' = switchBUp
       /\ timesSwitched' = timesSwitched
       /\ count' = count + 1
  ELSE /\ switchAUp' = switchAUp
       /\ switchBUp' = ~switchBUp
       /\ timesSwitched' = timesSwitched
       /\ count' = count

NonCounterAct(p) ==
  /\ p \in NonCounters
  /\ IF /\ ~switchAUp
        /\ timesSwitched[p] < 2
     THEN /\ switchAUp' = TRUE
          /\ switchBUp' = switchBUp
          /\ timesSwitched' = [ timesSwitched EXCEPT ![p] = @ + 1 ]
          /\ count' = count
     ELSE /\ switchAUp' = switchAUp
          /\ switchBUp' = ~switchBUp
          /\ timesSwitched' = timesSwitched
          /\ count' = count

Act(p) ==
  IF p = Counter THEN CounterAct ELSE NonCounterAct(p)

Next ==
  \E p \in Prisoner : Act(p)

(***********************
 * Sanity/typing       *
 ***********************)

TypeOK ==
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched \in [ NonCounters -> 0..2 ]
  /\ count \in 0..MaxCount

(***********************
 * Auxiliary invariant *
 ***********************)

(*
  CountInvariant ties the counter's tally to the aggregate number of
  upward flips performed by non-counters, with sensitivity to the
  current state of switch A. It captures that the counter may be ahead
  by at most one (due to an initial unknown A=Up), and when A is Up,
  there must be at least as many upward flips as increments already made.
*)
CountInvariant ==
  LET ups == TotalUps IN
  /\ count <= ups + 1
  /\ switchAUp => count <= ups
  /\ ups <= 2 * (Cardinality(Prisoner) - 1)

(***********************
 * Specification       *
 ***********************)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Prisoner : WF_vars(Act(p))

(***********************
 * Properties          *
 ***********************)

(*
  Safety: A declaration (Done) can only occur when
  every non-counter has flipped A up at least once.
*)
Safety ==
  [] ( Done => \A p \in NonCounters : timesSwitched[p] >= 1 )

(*
  Liveness: Eventually, Done is reached.
*)
Liveness == <> Done

=============================================================================