------------------------------ MODULE IncrementSpec ------------------------------
EXTENDS Naturals

CONSTANTS ProcA, ProcB
ProcessSet == {ProcA, ProcB}

VARIABLE x, pc

vars == <<x, pc>>

Init ==
  /\ x = 0
  /\ pc = [p \in ProcessSet |-> "Start"]

ProcAction(p) ==
  /\ pc[p] = "Start"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminate ==
  /\ ALL p \in ProcessSet : pc[p] = "Done"
  /\ UNCHANGED <<x, pc>>

Next == (∃p \in ProcessSet : ProcAction(p)) \/ Terminate

Spec == Init /\ [][Next]_vars /\ <> (ALL p \in ProcessSet : pc[p] = "Done")

=============================================================================