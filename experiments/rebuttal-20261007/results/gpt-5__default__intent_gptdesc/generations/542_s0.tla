---------------------------- MODULE TwoWorkersCounter ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Workers
ASSUME Workers = {1, 2}

VARIABLES counter, finished

vars == << counter, finished >>

Init ==
  /\ counter = 0
  /\ finished = [w \in Workers |-> FALSE]

Inc(i) ==
  /\ i \in Workers
  /\ ~finished[i]
  /\ counter' = counter + 1
  /\ finished' = [finished EXCEPT ![i] = TRUE]

Next ==
  \E i \in Workers: Inc(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Workers: WF_vars(Inc(i))

AllDone == \A i \in Workers: finished[i]

DoneCount == Cardinality({ i \in Workers : finished[i] })

(*
  Safety invariants
*)
TypeInv ==
  /\ counter \in Int
  /\ finished \in [Workers -> BOOLEAN]

CounterMatchesFinished ==
  counter = DoneCount

CounterNeverDecreases ==
  [] (counter' >= counter)

WorkerStepsIncExactlyOne ==
  [] (\A i \in Workers: Inc(i) => counter' = counter + 1)

OnlyStateChangesAreWorkersOrStutter ==
  [] (UNCHANGED vars \/ \E i \in Workers: Inc(i))

(*
  Liveness properties
*)
Termination ==
  <> AllDone

FinalCountEqualsWorkersCompleted ==
  [] (AllDone => counter = Cardinality(Workers))

=============================================================================