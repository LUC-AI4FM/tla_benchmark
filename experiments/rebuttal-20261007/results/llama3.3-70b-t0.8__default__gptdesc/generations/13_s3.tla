```
MODULE RollingDeployment
EXTENDS Integers, Sequences

CONSTANTS Servers, UpdateTimeout
VARIABLES serverStatus, loadBalancer, updatingServer, updateComplete, coordinatorState

Init ==
  /\ serverStatus = [s \in Servers |-> " idle"]
  /\ loadBalancer = Servers
  /\ updatingServer = NULL
  /\ updateComplete = FALSE
  /\ coordinatorState = "idle"

Next ==
  \/ \* Coordinator steps
    (coordinatorState = "idle" /\ 
     updatingServer = NULL /\ 
     coordinatorState' = "selecting" /\ 
     updatingServer' \in loadBalancer /\ 
     serverStatus' = [serverStatus EXCEPT ![updatingServer'] = "updating"] /\ 
     loadBalancer' = loadBalancer \ {updatingServer'} /\ 
     updateComplete' = FALSE)
  \/ (coordinatorState = "selecting" /\ 
      updateComplete = TRUE /\ 
      coordinatorState' = "restoring" /\ 
      serverStatus' = [serverStatus EXCEPT ![updatingServer] = "idle"] /\ 
      loadBalancer' = loadBalancer \cup {updatingServer} /\ 
      updatingServer' = NULL /\ 
      updateComplete' = FALSE)
  \/ (coordinatorState = "restoring" /\ 
      coordinatorState' = "idle")
  \/ \* Update process steps
    (serverStatus[updatingServer] = "updating" /\ 
     updateComplete' = TRUE /\ 
     serverStatus' = [serverStatus EXCEPT ![updatingServer] = "updated"] /\ 
     updatingServer' = updatingServer /\ 
     coordinatorState' = coordinatorState)

Spec ==
  Init /\ [][Next]_<<serverStatus, loadBalancer, updatingServer, updateComplete, coordinatorState>>
  /\ WF_(coordinatorState = "idle", coordinatorState = "selecting")
  /\ WF_(updateComplete = FALSE, updateComplete = TRUE)
  /\ []<>(coordinatorState = "restoring")

THEOREM Spec => []<>~(updateComplete = FALSE)
```