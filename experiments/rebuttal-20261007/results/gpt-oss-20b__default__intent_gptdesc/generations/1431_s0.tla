MODULE TwoStateController
EXTENDS Naturals, Sequences, TemporalOperators

CONSTANT MaxHistory \in Nat

VARIABLES state, history

ModeSet == {"M1", "M2"}

OtherMode(m) == IF m = "M1" THEN "M2" ELSE "M1"

Init ==
  /\ state = "M1"
  /\ history = <<>>

Switch ==
  /\ Len(history) < MaxHistory
  /\ state \in ModeSet
  /\ state' = OtherMode(state)
  /\ history' = Append(history, state)

Stay ==
  /\ state \in ModeSet
  /\ state' = state
  /\ history' = history

Terminate ==
  /\ state \in ModeSet
  /\ state' = "Done"
  /\ history' = history

Next == Switch \/ Stay \/ Terminate

vars == <<state, history>>

Fairness == WF_vars(Switch)

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInv == Len(history) < MaxHistory

LivenessProp == <> (state = "Done")

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessProp