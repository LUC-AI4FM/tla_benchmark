---------------------------- MODULE RollingDeployment ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Server, OldVersion, NewVersion

VARIABLES
    serverVersion,      \* Function: Server -> {OldVersion, NewVersion}
    serverState,        \* Function: Server -> {"ready", "updating"}
    loadBalancer,       \* Set of servers currently behind the load balancer
    phase,              \* Deployment phase: "init", "phase1", "phase2", "done"
    serverToUpdate      \* The server being updated in phase 1

vars == <<serverVersion, serverState, loadBalancer, phase, serverToUpdate>>

Servers == {"s1", "s2", "s3"}

TypeOK ==
    /\ serverVersion \in [Servers -> {OldVersion, NewVersion}]
    /\ serverState \in [Servers -> {"ready", "updating"}]
    /\ loadBalancer \subseteq Servers
    /\ phase \in {"init", "phase1_remove", "phase1_updating", "phase1_updated", 
                  "phase2_switch", "phase2_updating", "done"}
    /\ serverToUpdate \in Servers \cup {CHOOSE x : x \notin Servers}

Init ==
    /\ serverVersion = [s \in Servers |-> OldVersion]
    /\ serverState = [s \in Servers |-> "ready"]
    /\ loadBalancer = Servers
    /\ phase = "init"
    /\ serverToUpdate = CHOOSE s \in Servers : TRUE

\* Phase 1: Remove one server from load balancer
Phase1Remove ==
    /\ phase = "init"
    /\ serverToUpdate \in Servers
    /\ loadBalancer' = loadBalancer \ {serverToUpdate}
    /\ phase' = "phase1_remove"
    /\ UNCHANGED <<serverVersion, serverState, serverToUpdate>>

\* Phase 1: Start updating the removed server
Phase1StartUpdate ==
    /\ phase = "phase1_remove"
    /\ serverState' = [serverState EXCEPT ![serverToUpdate] = "updating"]
    /\ phase' = "phase1_updating"
    /\ UNCHANGED <<serverVersion, loadBalancer, serverToUpdate>>

\* Phase 1: Complete updating the removed server
Phase1CompleteUpdate ==
    /\ phase = "phase1_updating"
    /\ serverState[serverToUpdate] = "updating"
    /\ serverVersion' = [serverVersion EXCEPT ![serverToUpdate] = NewVersion]
    /\ serverState' = [serverState EXCEPT ![serverToUpdate] = "ready"]
    /\ phase' = "phase1_updated"
    /\ UNCHANGED <<loadBalancer, serverToUpdate>>

\* Phase 2: Switch load balancer to updated server, start updating others
Phase2Switch ==
    /\ phase = "phase1_updated"
    /\ loadBalancer' = {serverToUpdate}
    /\ phase' = "phase2_switch"
    /\ UNCHANGED <<serverVersion, serverState, serverToUpdate>>

\* Phase 2: Start updating remaining servers (not behind LB now)
Phase2StartUpdating ==
    /\ phase = "phase2_switch"
    /\ LET others == Servers \ {serverToUpdate}
       IN serverState' = [s \in Servers |-> IF s \in others THEN "updating" ELSE serverState[s]]
    /\ phase' = "phase2_updating"
    /\ UNCHANGED <<serverVersion, loadBalancer, serverToUpdate>>

\* Phase 2: Complete update of one remaining server
Phase2CompleteOneUpdate(s) ==
    /\ phase = "phase2_updating"
    /\ s \in Servers \ {serverToUpdate}
    /\ serverState[s] = "updating"
    /\ serverVersion' = [serverVersion EXCEPT ![s] = NewVersion]
    /\ serverState' = [serverState EXCEPT ![s] = "ready"]
    /\ UNCHANGED <<loadBalancer, phase, serverToUpdate>>

\* Check if all servers except serverToUpdate are updated
AllOthersUpdated ==
    \A s \in Servers \ {serverToUpdate} : 
        /\ serverVersion[s] = NewVersion 
        /\ serverState[s] = "ready"

\* Phase 2: Add updated servers back to load balancer and finish
Phase2Complete ==
    /\ phase = "phase2_updating"
    /\ AllOthersUpdated
    /\ loadBalancer' = Servers
    /\ phase' = "done"
    /\ UNCHANGED <<serverVersion, serverState, serverToUpdate>>

\* Termination - system is done
Terminated ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ Phase1Remove
    \/ Phase1StartUpdate
    \/ Phase1CompleteUpdate
    \/ Phase2Switch
    \/ Phase2StartUpdating
    \/ \E s \in Servers : Phase2CompleteOneUpdate(s)
    \/ Phase2Complete
    \/ Terminated

\* Fairness to ensure termination
Fairness ==
    /\ WF_vars(Phase1Remove)
    /\ WF_vars(Phase1StartUpdate)
    /\ WF_vars(Phase1CompleteUpdate)
    /\ WF_vars(Phase2Switch)
    /\ WF_vars(Phase2StartUpdating)
    /\ \A s \in Servers : WF_vars(Phase2CompleteOneUpdate(s))
    /\ WF_vars(Phase2Complete)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Zero Downtime - at least one server in LB is not updating
ZeroDowntime ==
    \E s \in loadBalancer : serverState[s] = "ready"

\* Safety: Same Version - all servers in LB have same version
SameVersion ==
    \A s1, s2 \in loadBalancer : serverVersion[s1] = serverVersion[s2]

\* Liveness: Termination - eventually all servers updated
Termination ==
    <>(phase = "done" /\ \A s \in Servers : serverVersion[s] = NewVersion)

=============================================================================