```
MODULE TwoPhaseCommit
EXTENDS Integers, TLC

CONSTANTS Participants
VARIABLES participantState

Init ==
  participantState = [p \in Participants |-> "neutral"]

Next ==
  (\E p \in Participants :
    (participantState[p] = "neutral" /\ 
     participantState' = [participantState EXCEPT ![p] = "prepared"]) \/
    (participantState[p] = "prepared" /\ 
     (\A q \in Participants : participantState[q] = "prepared") /\ 
     participantState' = [participantState EXCEPT ![p] = "committed"]) \/
    (participantState[p] = "prepared" /\ 
     (\E q \in Participants : participantState[q] = "aborted") /\ 
     participantState' = [participantState EXCEPT ![p] = "aborted"]) \/
    (participantState[p] = "neutral" /\ 
     (\E q \in Participants : participantState[q] = "aborted") /\ 
     participantState' = [participantState EXCEPT ![p] = "aborted"])))

Spec ==
  Init /\ [][Next]_participantState

TypeSafety ==
  \A p \in Participants : participantState[p] \in {"neutral", "prepared", "committed", "aborted"}

Agreement ==
  \A p, q \in Participants :
    (participantState[p] = "committed") => (participantState[q] # "aborted")

LivenessSafety ==
  <>(\A p \in Participants : participantState[p] = "prepared") => <>(\E p \in Participants : participantState[p] = "committed")

THEOREM Spec => []TypeSafety
THEOREM Spec => []Agreement
THEOREM Spec => LivenessSafety
```
Note: The above TLA+ specification uses the `TLC` module for temporal logic and assumes that the `Participants` constant is a set of participant identifiers. The `participantState` variable maps each participant to its current state, which can be one of "neutral", "prepared", "committed", or "aborted". The `Next` action describes the possible state transitions for each participant, and the `Spec` formula defines the overall specification as the conjunction of the initial condition and the next-state relation. The `TypeSafety`, `Agreement`, and `LivenessSafety` formulas define the required correctness properties as invariants.