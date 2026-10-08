```
MODULE TwoPhaseCommit
VARIABLES state, decided

RM == {"p1", "p2", ...} \* set of participant identifiers (resource managers)

r2(s) == {<<p, s[p]>> : p \in RM}

TCTypeOK == (\A p \in RM : state[p] \in {"neutral", "prepared", "committed", "aborted"})

TCConsistent == (\A p1, p2 \in RM : (decided[p1] = "commit") /\ (decided[p2] = "abort") => FALSE)

TCSpec == 
  /\ state = [p \in RM |-> "neutral"]
  /\ decided = [p \in RM |-> NULL]
  /\ [][
      \/ (\E p \in RM : 
          state[p] = "neutral" 
          /\ state' = [state EXCEPT ![p] = "prepared"]
          /\ decided' = decided)
      \/ (\E p \in RM : 
          state[p] = "prepared" 
          /\ \A q \in RM : (decided[q] = NULL) 
          /\ (\E q \in RM : state[q] = "neutral")
          /\ state' = [state EXCEPT ![p] = "aborted"]
          /\ decided' = [decided EXCEPT ![p] = "abort"])
      \/ (\E p \in RM : 
          state[p] = "prepared" 
          /\ \A q \in RM : (decided[q] = NULL) 
          /\ \A q \in RM : (state[q] = "prepared")
          /\ state' = [state EXCEPT ![p] = "committed"]
          /\ decided' = [decided EXCEPT ![p] = "commit"])
      \/ (\E p \in RM : 
          state[p] = "neutral" 
          /\ \A q \in RM : (decided[q] = NULL) 
          /\ (\E q \in RM : state[q] = "aborted")
          /\ state' = [state EXCEPT ![p] = "aborted"]
          /\ decided' = [decided EXCEPT ![p] = "abort"])
      ]
  /\ []TCTypeOK
  /\ []TCConsistent
  /\ <>(\A p \in RM : (state[p] = "prepared") => <>(\E q \in RM : (decided[q] = "commit")))

THEOREM TCSpec => []TCTypeOK
THEOREM TCSpec => []TCConsistent
THEOREM TCSpec => <>(\A p \in RM : (state[p] = "prepared") => <>(\E q \in RM : (decided[q] = "commit")))
```
Note: The `...` in the definition of `RM` should be replaced with the actual set of participant identifiers. This specification uses a simple encoding for the states and decisions, but it can be modified to use more complex encodings if needed.