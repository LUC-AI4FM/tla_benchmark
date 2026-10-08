```
MODULE NBAC
EXTENDS Integers, TLC

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
    /\ msgBuffer[p] = {}
    /\ crashed[p] = FALSE
    /\ fd[p] = {}
    /\ state' = [state EXCEPT ![p] = "yes"]
    /\ vote' = vote
    /\ msgBuffer' = msgBuffer
    /\ crashed' = crashed
    /\ fd' = fd
  \/ \E p \in ProcSet :
    /\ state[p] = "init"
    /\ vote[p] = "no"
    /\ msgBuffer[p] = {}
    /\ crashed[p] = FALSE
    /\ fd[p] = {}
    /\ state' = [state EXCEPT ![p] = "no"]
    /\ vote' = vote
    /\ msgBuffer' = msgBuffer
    /\ crashed' = crashed
    /\ fd' = fd
  \/ \E p \in ProcSet, q \in ProcSet :
    /\ state[p] = "yes"
    /\ vote[q] = "yes"
    /\ msgBuffer[p] = {}
    /\ crashed[p] = FALSE
    /\ fd[p] = {}
    /\ state' = [state EXCEPT ![p] = "commit"]
    /\ vote' = vote
    /\ msgBuffer' = [msgBuffer EXCEPT ![p] = {"commit"}]
    /\ crashed' = crashed
    /\ fd' = fd
  \/ \E p \in ProcSet, q \in ProcSet :
    /\ state[p] = "no"
    /\ vote[q] = "no"
    /\ msgBuffer[p] = {}
    /\ crashed[p] = FALSE
    /\ fd[p] = {}
    /\ state' = [state EXCEPT ![p] = "abort"]
    /\ vote' = vote
    /\ msgBuffer' = [msgBuffer EXCEPT ![p] = {"abort"}]
    /\ crashed' = crashed
    /\ fd' = fd
  \/ \E p \in ProcSet :
    /\ crashed[p] = FALSE
    /\ state' = state
    /\ vote' = vote
    /\ msgBuffer' = msgBuffer
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ fd' = fd

Spec ==
  Init /\ [][Next]_state /\ [][Next]_vote /\ [][Next]_msgBuffer /\ [][Next]_crashed /\ [][Next]_fd

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []ValidityCondition

TypeCorrectness == 
  /\ state \in [ProcSet -> {"init", "yes", "no", "commit", "abort"}]
  /\ vote \in [ProcSet -> {"yes", "no"}]
  /\ msgBuffer \in [ProcSet -> SUBSET MsgType]
  /\ crashed \in [ProcSet -> BOOLEAN]
  /\ fd \in [ProcSet -> ProcSet]

ValidityCondition == 
  \A p \in ProcSet : state[p] = "commit" => \A q \in ProcSet : vote[q] = "yes"
```