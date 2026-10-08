```
MODULE RollingDeployment
EXTENDS Integers, TLC

CONSTANTS ServerSet, VersionSet
VARIABLES loadBalancer, serverStatus, updatePhase, version

Init ==
  /\ loadBalancer = ServerSet
  /\ serverStatus = [s \in ServerSet |-> "idle"]
  /\ updatePhase = "start"
  /\ version = "old"

Next ==
  /\ IF updatePhase = "start"
    THEN
      /\ updatePhase' = "remove"
      /\ serverStatus' = [serverStatus EXCEPT ![s] = "updating"]
      /\ loadBalancer' = ServerSet \ {s}
    ELSEIF updatePhase = "remove"
    THEN
      /\ updatePhase' = "updateOthers"
      /\ serverStatus' = [serverStatus EXCEPT ![^s] = "updating"]
      /\ loadBalancer' = loadBalancer
    ELSEIF updatePhase = "updateOthers"
    THEN
      /\ updatePhase' = "switch"
      /\ serverStatus' = [serverStatus EXCEPT ![s'] = "updated"]
      /\ loadBalancer' = ServerSet \ {s'}
    ELSEIF updatePhase = "switch"
    THEN
      /\ updatePhase' = "complete"
      /\ serverStatus' = [serverStatus EXCEPT ![^s] = "updated"]
      /\ loadBalancer' = ServerSet
    ELSEIF updatePhase = "complete"
    THEN
      /\ updatePhase' = "done"
      /\ serverStatus' = serverStatus
      /\ loadBalancer' = loadBalancer
  /\ version' = IF updatePhase = "updateOthers" THEN "new" ELSE version

Spec ==
  /\ Init
  /\ [][Next]_loadBalancer, serverStatus, updatePhase, version
  /\ WF_vars(Next, loadBalancer, serverStatus, updatePhase, version)

ZeroDowntime ==
  \A s \in loadBalancer : serverStatus[s] # "updating"

SameVersion ==
  \A s1, s2 \in loadBalancer : version = "new" => serverStatus[s1] = serverStatus[s2]

Termination ==
  <>(updatePhase = "done")

THEOREM Spec => []ZeroDowntime
THEOREM Spec => []SameVersion
THEOREM Spec => Termination

```
Note: `s` and `s'` are placeholders for the specific servers being updated, which should be replaced with actual server identifiers in a concrete implementation. The `^s` notation represents all servers except `s`.