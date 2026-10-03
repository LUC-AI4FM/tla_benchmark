---------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Servers, UpdateTime
VARIABLES serverStatus, loadBalancer, updateProcess, coordinator

Init ==
  /\ serverStatus \in [Servers |-> "idle"]
  /\ loadBalancer = Servers
  /\ updateProcess = [s \in Servers |-> FALSE]
  /\ coordinator = "idle"

UpdateStep(s) ==
  /\ serverStatus' = [serverStatus EXCEPT ![s] = "updating"]
  /\ updateProcess' = [updateProcess EXCEPT ![s] = TRUE]
  /\ loadBalancer' = loadBalancer
  /\ coordinator' = coordinator

CoordinatorStep ==
  /\ \E s \in Servers :
      /\ serverStatus'[s] = "updated"
      /\ updateProcess' = [updateProcess EXCEPT ![s] = FALSE]
      /\ loadBalancer' = loadBalancer \ {s}
      /\ coordinator' = "updating"
  \/ /\ \A s \in Servers : serverStatus[s] = "updated"
      /\ loadBalancer' = Servers
      /\ coordinator' = "done"

Next ==
  (\E s \in Servers : updateProcess[s] = FALSE /\ UpdateStep(s))
  \/ CoordinatorStep

Spec == Init /\ [][Next]_<<serverStatus, loadBalancer, updateProcess, coordinator>>
=============================================================================