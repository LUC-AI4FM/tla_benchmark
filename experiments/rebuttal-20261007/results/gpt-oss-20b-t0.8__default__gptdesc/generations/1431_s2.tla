MODULE TwoStateProcess
EXTENDS Sequences

CONSTANTS AVal, BVal, DoneVal, HistoryLimit

VARIABLES pc, history

(*-- initialization --------------------------------------------------------*)
Init ==
  /\ pc = AVal
  /\ history = <<>>

(*-- actions --------------------------------------------------------------*)
MoveA ==
  /\ pc = AVal
  /\ pc' = BVal
  /\ history' = Append(history, AVal)

MoveB ==
  /\ pc = BVal
  /\ pc' = AVal
  /\ history' = history

Stutter ==
  /\ pc' = pc
  /\ history' = history

Next == MoveA \/ MoveB \/ Stutter

(*-- safety invariants ----------------------------------------------------*)
Safety ==
  /\ Len(history) <= HistoryLimit
  /\ pc \in {AVal, BVal}

(*-- specification --------------------------------------------------------*)
Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(MoveA \/ MoveB)
  /\ Safety
  /\ <> (pc = DoneVal)

===============================================================================