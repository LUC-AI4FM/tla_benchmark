```
MODULE RollingDeployment
EXTENDS Integers, FiniteSets

CONSTANTS Servers, UpdateTime
VARIABLES serverStatus, loadBalancer, updatingServer, coordinatorStatus, updateComplete

Init ==
  /\ serverStatus \in [Servers |-> "idle"]
  /\ loadBalancer = Servers
  /\ updatingServer = NULL
  /\ coordinatorStatus = "idle"
  /\ updateComplete = {}

Next ==
  /\ (coordinatorStatus = "idle") => 
    /\ updatingServer' = CHOOSE s \in (Servers \cup {NULL}) : s \notin loadBalancer'
    /\ IF updatingServer' = NULL THEN coordinatorStatus' = "done" ELSE coordinatorStatus' = "updating"
    /\ loadBalancer' = loadBalancer \ {updatingServer'}
  /\ (coordinatorStatus = "updating") => 
    /\ updateComplete' = updateComplete \cup {updatingServer}
    /\ IF updatingServer \in updateComplete' THEN 
      /\ loadBalancer' = loadBalancer \cup {updatingServer}
      /\ coordinatorStatus' = "idle"
    ELSE 
      /\ loadBalancer' = loadBalancer
      /\ coordinatorStatus' = "updating"
  /\ (coordinatorStatus = "done") => 
    /\ UNCHANGED <<serverStatus, loadBalancer, updatingServer, coordinatorStatus, updateComplete>>
  /\ serverStatus' = [s \in Servers |-> IF s = updatingServer THEN "updating" ELSE @]

Spec == Init /\ [][Next]_<<serverStatus, loadBalancer, updatingServer, coordinatorStatus, updateComplete>>

THEOREM Spec => []<>(coordinatorStatus = "done")
WF_Vars == <<updatingServer, coordinatorStatus>>
Fairness == WF_coordinator(coordinatorStatus) /\ SF_update(updatingServer)

WF_coordinator == 
  /\ []<>(coordinatorStatus = "idle" => <>~(coordinatorStatus = "idle"))
  /\ []<>(coordinatorStatus = "updating" => <>~(coordinatorStatus = "updating"))

SF_update == 
  /\ []<>(updatingServer /= NULL => <>(updatingServer = NULL))

INV == 
  /\ serverStatus \in [Servers |-> {"idle", "updating"}]
  /\ loadBalancer \subseteq Servers
  /\ updatingServer \in (Servers \cup {NULL})
  /\ coordinatorStatus \in {"idle", "updating", "done"}
  /\ updateComplete \subseteq Servers

THEOREM Spec => INV
```