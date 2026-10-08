MODULE TwoProcInc
EXTENDS Naturals

CONSTANTS ProcA, ProcB
ProcSet == {ProcA, ProcB}

VARIABLES x, pc

Init ==
  /\ x = 0
  /\ pc = [p \in ProcSet |-> 0]

AllDone ==
  \A p \in ProcSet : pc[p] = 1

Inc(p) ==
  /\ p \in ProcSet
  /\ pc[p] = 0
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![p] = 1]

TerminateAll ==
  /\ AllDone
  /\ UNCHANGED <<x, pc>>

Next ==
  \/ \E p \in ProcSet : Inc(p)
  \/ TerminateAll

Spec ==
  Init /\ [][Next]_<<x, pc>> /\ []<>(AllDone)