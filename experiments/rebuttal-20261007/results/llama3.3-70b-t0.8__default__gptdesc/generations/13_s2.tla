```tla
MODULE RollingDeployment
EXTENDS Integers, FiniteSets

CONSTANTS NumServers, UpdateTime
VARIABLES serverStatus, 
          loadBalancer,
          updateProcess,
          coordinator,
          completedUpdates,
          currentServer

Init == 
  /\ serverStatus = [i \in 1..NumServers |-> "pending"]
  /\ loadBalancer = {}
  /\ updateProcess = "idle"
  /\ coordinator = "idle"
  /\ completedUpdates = 0
  /\ currentServer = 1

Next == 
  /\ IF (updateProcess = "idle") THEN 
       /\ updateProcess = "running"
       /\ loadBalancer = {}
       /\ serverStatus[currentServer] = "updating"
     ELSE 
       /\ updateProcess = "idle"
       /\ serverStatus[currentServer] = "updated"
       /\ completedUpdates = completedUpdates + 1
  /\ IF (coordinator = "idle") THEN 
       /\ coordinator = "running"
       /\ currentServer = IF (currentServer < NumServers) THEN currentServer + 1 ELSE 1
     ELSE 
       /\ coordinator = "idle"
       /\ loadBalancer = loadBalancer \cup {currentServer}

Spec == Init /\ [][Next]_serverStatus

Termination == completedUpdates = NumServers

WeakFairnessUpdate == WF_vars(updateProcess, serverStatus)
WeakFairnessCoordinator == WF_vars(coordinator, currentServer)

THEOREM Spec => []Termination
THEOREM Spec => WeakFairnessUpdate
THEOREM Spec => WeakFairnessCoordinator
```