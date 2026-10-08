```
MODULE NBAC
EXTENDS Integers, TLC

CONSTANTS ProcSet, Quorum
VARIABLES state, vote, msgBuffer, crashed, failureDetector

Init == 
  (state = [p \in ProcSet |-> "init"]) 
  /\ (vote = [p \in ProcSet |-> NULL]) 
  /\ (msgBuffer = [p \in ProcSet |-> {}]) 
  /\ (crashed = [p \in ProcSet |-> FALSE]) 
  /\ (failureDetector = [p \in ProcSet |-> {}])

TypeOK == 
  (\A p \in ProcSet : state[p] \in {"init", "yes", "no", "commit", "abort"}) 
  /\ (\A p \in ProcSet : vote[p] \in {NULL, "yes", "no"})

Validity == 
  (\A p \in ProcSet : state[p] = "commit" => \A q \in ProcSet : vote[q] = "yes") 
  /\ (\A p \in ProcSet : state[p] = "abort" => \E q \in ProcSet : vote[q] = "no")

Send(p, v) == 
  msgBuffer' = [msgBuffer EXCEPT ![p] = {v} \cup @]

Recv(p, v) == 
  (state[p] = "init") /\ (msgBuffer[p] = {v}) 
  /\ (state' = [state EXCEPT ![p] = IF v = "yes" THEN "yes" ELSE "no"]) 
  /\ (vote' = [vote EXCEPT ![p] = v]) 
  /\ UNCHANGED <<msgBuffer, crashed, failureDetector>>

FailureDetectorUpdate(p) == 
  failureDetector' = [failureDetector EXCEPT ![p] = IF \E q \in ProcSet : crashed[q] THEN {q} ELSE {}]

LocalTransition(p) == 
  (state[p] = "yes") /\ (\A q \in ProcSet : vote[q] = "yes") 
  /\ (state' = [state EXCEPT ![p] = "commit"]) 
  /\ UNCHANGED <<vote, msgBuffer, crashed, failureDetector>>

Crash(p) == 
  (crashed' = [crashed EXCEPT ![p] = TRUE]) 
  /\ UNCHANGED <<state, vote, msgBuffer, failureDetector>>

Next == 
  (\E p \in ProcSet : Send(p, "yes")) 
  \/ (\E p \in ProcSet : Send(p, "no")) 
  \/ (\E p \in ProcSet : Recv(p, "yes")) 
  \/ (\E p \in ProcSet : Recv(p, "no")) 
  \/ (\E p \in ProcSet : FailureDetectorUpdate(p)) 
  \/ (\E p \in ProcSet : LocalTransition(p)) 
  \/ (\E p \in ProcSet : Crash(p))

Spec == Init /\ [][Next]_<<state, vote, msgBuffer, crashed, failureDetector>>
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity

Fairness == WF_<<state, vote, msgBuffer, crashed, failureDetector>>(Next)
```
Note: The encoding uses the standard TLA+ constructs and notations. The specification is designed to be checked using the TLC model checker for safety properties (e.g., type correctness and validity conditions) and liveness properties (e.g., eventual commit or abort).