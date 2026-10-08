```
MODULE RollingUpdate
EXTENDS Integers, FiniteSets

CONSTANTS Servers, OldVersion, NewVersion, Updating

VARIABLES loadBalanced, updatingServers, serverVersions

Init ==
  /\ loadBalanced = Servers
  /\ updatingServers = {}
  /\ serverVersions = [s \in Servers |-> OldVersion]

Next ==
  \/ RemoveFromLoadBalancer
  \/ UpdateServer
  \/ ReturnToService
  \/ OrchestratorWait

RemoveFromLoadBalancer ==
  /\ ~updatingServers = {}
  /\ loadBalanced' = loadBalanced \ {s}
  /\ updatingServers' = updatingServers \cup {s}
  /\ serverVersions' = [serverVersions EXCEPT ![s] = Updating]
  /\ s \in loadBalanced

UpdateServer ==
  /\ s \in updatingServers
  /\ serverVersions' = [serverVersions EXCEPT ![s] = NewVersion]
  /\ updatingServers' = updatingServers \ {s}
  /\ loadBalanced' = loadBalanced
  /\ s \in Servers

ReturnToService ==
  /\ s \in updatingServers
  /\ serverVersions[s] = NewVersion
  /\ loadBalanced' = loadBalanced \cup {s}
  /\ updatingServers' = updatingServers \ {s}
  /\ serverVersions' = serverVersions

OrchestratorWait ==
  /\ ~updatingServers = {}
  /\ loadBalanced' = loadBalanced
  /\ updatingServers' = updatingServers
  /\ serverVersions' = serverVersions

Spec == Init /\ [][Next]_<<loadBalanced, updatingServers, serverVersions>>
           /\ WF_<<loadBalanced, updatingServers, serverVersions>>(RemoveFromLoadBalancer)
           /\ SF_<<loadBalanced, updatingServers, serverVersions>>(UpdateServer)

THEOREM Spec => []HomogeneousVersion
THEOREM Spec => []ZeroDowntime
THEOREM Spec => <>[]AllUpdated

HomogeneousVersion ==
  \A s1, s2 \in loadBalanced : serverVersions[s1] = serverVersions[s2]

ZeroDowntime ==
  loadBalanced # {}

AllUpdated ==
  \A s \in Servers : serverVersions[s] = NewVersion
```