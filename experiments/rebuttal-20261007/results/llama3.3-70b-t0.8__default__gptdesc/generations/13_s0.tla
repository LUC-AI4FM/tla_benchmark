```
MODULE RollingDeployment
EXTENDS Integers, FiniteSets

CONSTANTS Servers, UpdateTime
VARIABLES serverStatus, loadBalancer, updatingServer, coordinatorStatus, updateComplete

Init == (
  /\ serverStatus \in [Servers -> {"idle", "updating", "updated"}]
  /\ loadBalancer \in SUBSET Servers
  /\ updatingServer = NULL
  /\ coordinatorStatus = "idle"
  /\ updateComplete = {}
)

TypeInvariant == (
  /\ serverStatus \in [Servers -> {"idle", "updating", "updated"}]
  /\ loadBalancer \in SUBSET Servers
  /\ (updatingServer # NULL) => (updatingServer \in Servers)
  /\ coordinatorStatus \in {"idle", "removing", "waiting", "restoring"}
  /\ updateComplete \subseteq Servers
)

Next == (
  /\ IF coordinatorStatus = "idle" THEN 
    /\ updatingServer = CHOOSE s \in Servers : serverStatus[s] = "idle"
    /\ loadBalancer := loadBalancer \ {updatingServer}
    /\ serverStatus := [serverStatus EXCEPT ![updatingServer] = "updating"]
    /\ coordinatorStatus := "waiting"
  ELSEIF coordinatorStatus = "waiting" THEN 
    /\ IF updateComplete = Servers THEN
        /\ loadBalancer := Servers
        /\ coordinatorStatus := "idle"
      ELSE
        /\ updatingServer := CHOOSE s \in (Servers \ updateComplete) : serverStatus[s] = "updating"
        /\ updateComplete := updateComplete \cup {updatingServer}
        /\ serverStatus := [serverStatus EXCEPT ![updatingServer] = "updated"]
        /\ coordinatorStatus := "restoring"
    /\ loadBalancer := loadBalancer \cup {updatingServer}
  ELSEIF coordinatorStatus = "restoring" THEN 
    /\ updatingServer := CHOOSE s \in Servers : serverStatus[s] = "updated"
    /\ serverStatus := [serverStatus EXCEPT ![updatingServer] = "idle"]
    /\ coordinatorStatus := "idle"
)

Spec == Init /\ [][Next]_<<serverStatus, loadBalancer, updatingServer, coordinatorStatus, updateComplete>>
WF_coordinator == WF_vars(coordinatorStatus)
WF_updater == WF_vars(updatingServer)
THEOREM Spec => []TypeInvariant
THEOREM Spec => (<>(updateComplete = Servers)) 
```