```
MODULE NBAC
EXTENDS Integers, FiniteSets

CONSTANTS ProcSet, Quorum
VARIABLES state, vote, msgBuffer, crashed, fd

Init ==
  /\ state \in [ProcSet -> {"init", "yes", "no", "commit", "abort"}]
  /\ vote \in [ProcSet -> {"yes", "no"}]
  /\ msgBuffer \in [ProcSet -> SUBSET MsgType]
  /\ crashed \in [ProcSet -> BOOLEAN]
  /\ fd \in [ProcSet -> ProcSet]

Next ==
  \/ \E p \in ProcSet :
    /\ state[p] = "init"
    /\ vote[p] = "yes"
    /\ msgBuffer' = [msgBuffer EXCEPT ![p] = {}]
    /\ crashed' = crashed
    /\ fd' = fd
    /\ state' = [state EXCEPT ![p] = "yes"]
  \/ \E p \in ProcSet :
    /\ state[p] = "init"
    /\ vote[p] = "no"
    /\ msgBuffer' = [msgBuffer EXCEPT ![p] = {}]
    /\ crashed' = crashed
    /\ fd' = fd
    /\ state' = [state EXCEPT ![p] = "no"]
  \/ \E p \in ProcSet :
    /\ state[p] \in {"yes", "no"}
    /\ msgBuffer[p] /= {}
    /\ \E m \in msgBuffer[p] : 
      /\ IF m.type = "vote" THEN
        /\ vote' = [vote EXCEPT ![p] = m.value]
        /\ msgBuffer' = [msgBuffer EXCEPT ![p] = msgBuffer[p] \ {m}]
      ELSE
        /\ msgBuffer' = [msgBuffer EXCEPT ![p] = msgBuffer[p] \ {m}]
      /\ crashed' = crashed
      /\ fd' = fd
      /\ state' = state
  \/ \E p \in ProcSet :
    /\ state[p] \in {"yes", "no"}
    /\ fd'[p] /= {}
    /\ \E q \in fd'[p] : 
      /\ crashed' = [crashed EXCEPT ![q] = TRUE]
      /\ msgBuffer' = msgBuffer
      /\ vote' = vote
      /\ state' = state
      /\ fd' = [fd EXCEPT ![p] = fd[p] \ {q}]
  \/ \E p \in ProcSet :
    /\ state[p] = "yes"
    /\ \A q \in ProcSet : vote[q] = "yes"
    /\ state' = [state EXCEPT ![p] = "commit"]
    /\ msgBuffer' = msgBuffer
    /\ crashed' = crashed
    /\ fd' = fd
    /\ vote' = vote

Spec == Init /\ [][Next]_<<state, vote, msgBuffer, crashed, fd>>

THEOREM Spec => []\A p \in ProcSet : state[p] /= "commit" \/ \A q \in ProcSet : vote[q] = "yes"
```