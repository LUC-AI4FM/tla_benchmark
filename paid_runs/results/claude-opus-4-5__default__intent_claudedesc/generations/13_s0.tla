-------------------------------- MODULE RollingDeployment --------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS V1, V2

VARIABLES
    serverState,      \* Function from server -> "ready" | "updating"
    serverVersion,    \* Function from server -> V1 | V2
    loadBalancer,     \* Set of servers currently in the load balancer
    phase,            \* "init" | "phase1_remove" | "phase1_update" | "phase2_switch" | "phase2_update" | "done"
    targetServer      \* The server being updated in phase 1 (removed from LB first)

Servers == {1, 2, 3}
OtherServers == Servers \ {1}  \* Servers 2 and 3 are updated in phase 2

TypeOK ==
    /\ serverState \in [Servers -> {"ready", "updating"}]
    /\ serverVersion \in [Servers -> {V1, V2}]
    /\ loadBalancer \subseteq Servers
    /\ phase \in {"init", "phase1_remove", "phase1_update", "phase2_switch", "phase2_update", "done"}
    /\ targetServer \in Servers

Init ==
    /\ serverState = [s \in Servers |-> "ready"]
    /\ serverVersion = [s \in Servers |-> V1]
    /\ loadBalancer = Servers
    /\ phase = "init"
    /\ targetServer = 1

\* Phase 1: Remove target server from load balancer
RemoveTargetFromLB ==
    /\ phase = "init"
    /\ phase' = "phase1_remove"
    /\ loadBalancer' = loadBalancer \ {targetServer}
    /\ UNCHANGED <<serverState, serverVersion, targetServer>>

\* Phase 1: Start updating the removed server
StartUpdateTarget ==
    /\ phase = "phase1_remove"
    /\ serverState[targetServer] = "ready"
    /\ phase' = "phase1_update"
    /\ serverState' = [serverState EXCEPT ![targetServer] = "updating"]
    /\ UNCHANGED <<serverVersion, loadBalancer, targetServer>>

\* Phase 1: Complete update on target server
CompleteUpdateTarget ==
    /\ phase = "phase1_update"
    /\ serverState[targetServer] = "updating"
    /\ serverState' = [serverState EXCEPT ![targetServer] = "ready"]
    /\ serverVersion' = [serverVersion EXCEPT ![targetServer] = V2]
    /\ phase' = "phase2_switch"
    /\ UNCHANGED <<loadBalancer, targetServer>>

\* Phase 2: Switch load balancer to the updated server, start updating others
SwitchLoadBalancer ==
    /\ phase = "phase2_switch"
    /\ serverVersion[targetServer] = V2
    /\ serverState[targetServer] = "ready"
    /\ loadBalancer' = {targetServer}
    /\ phase' = "phase2_update"
    /\ serverState' = [s \in Servers |-> IF s \in OtherServers THEN "updating" ELSE serverState[s]]
    /\ UNCHANGED <<serverVersion, targetServer>>

\* Phase 2: One of the other servers completes its update and rejoins LB
CompleteUpdateOther(s) ==
    /\ phase = "phase2_update"
    /\ s \in OtherServers
    /\ serverState[s] = "updating"
    /\ serverState' = [serverState EXCEPT ![s] = "ready"]
    /\ serverVersion' = [serverVersion EXCEPT ![s] = V2]
    /\ loadBalancer' = loadBalancer \cup {s}
    /\ UNCHANGED <<phase, targetServer>>

\* Transition to done when all servers are updated and in LB
FinishDeployment ==
    /\ phase = "phase2_update"
    /\ \A s \in Servers : serverState[s] = "ready" /\ serverVersion[s] = V2
    /\ loadBalancer = Servers
    /\ phase' = "done"
    /\ UNCHANGED <<serverState, serverVersion, loadBalancer, targetServer>>

Next ==
    \/ RemoveTargetFromLB
    \/ StartUpdateTarget
    \/ CompleteUpdateTarget
    \/ SwitchLoadBalancer
    \/ \E s \in OtherServers : CompleteUpdateOther(s)
    \/ FinishDeployment

\* Safety: Zero downtime - at least one server in LB is not updating
ZeroDowntime ==
    \E s \in loadBalancer : serverState[s] = "ready"

\* Safety: Same version - all servers in LB have the same version
SameVersion ==
    \A s1, s2 \in loadBalancer : serverVersion[s1] = serverVersion[s2]

\* Combined safety invariant
Safety == ZeroDowntime /\ SameVersion

\* Liveness: Eventually all servers are updated
AllUpdated ==
    /\ phase = "done"
    /\ \A s \in Servers : serverVersion[s] = V2 /\ serverState[s] = "ready"
    /\ loadBalancer = Servers

Termination == <>AllUpdated

\* Fairness: All actions must eventually be taken if enabled
Fairness ==
    /\ WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(RemoveTargetFromLB)
    /\ WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(StartUpdateTarget)
    /\ WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(CompleteUpdateTarget)
    /\ WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(SwitchLoadBalancer)
    /\ \A s \in OtherServers : WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(CompleteUpdateOther(s))
    /\ WF_<<serverState, serverVersion, loadBalancer, phase, targetServer>>(FinishDeployment)

Spec == Init /\ [][Next]_<<serverState, serverVersion, loadBalancer, phase, targetServer>> /\ Fairness

=========================================================================================