---------------------------- MODULE RollingDeploy ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Servers

ASSUME Servers # {}

VARIABLES 
    serverVersion,      \* serverVersion[s] \in {"old", "new"} - version running on each server
    serverStatus,       \* serverStatus[s] \in {"active", "draining", "updating", "ready"} - status of each server
    lbPool,             \* Set of servers currently in load balancer pool
    pendingUpdate,      \* Server currently being updated (or "none")
    updateRequested,    \* Whether coordinator has requested an update for pendingUpdate
    updateComplete,     \* Whether the server update process has completed
    coordState,         \* Coordinator state: "idle", "removing", "waiting", "restoring", "done"
    toUpdate,           \* Set of servers still needing update
    pc                  \* Program counter for processes

vars == <<serverVersion, serverStatus, lbPool, pendingUpdate, updateRequested, 
          updateComplete, coordState, toUpdate, pc>>

\* Type invariant
TypeOK ==
    /\ serverVersion \in [Servers -> {"old", "new"}]
    /\ serverStatus \in [Servers -> {"active", "draining", "updating", "ready"}]
    /\ lbPool \subseteq Servers
    /\ pendingUpdate \in Servers \cup {"none"}
    /\ updateRequested \in BOOLEAN
    /\ updateComplete \in BOOLEAN
    /\ coordState \in {"idle", "removing", "waiting", "restoring", "done"}
    /\ toUpdate \subseteq Servers
    /\ pc \in [{"coordinator"} \cup Servers -> {"coord_idle", "coord_select", "coord_remove", 
                                                  "coord_request", "coord_wait", "coord_restore", 
                                                  "coord_done", "server_idle", "server_updating", 
                                                  "server_done"}]

\* Initial state
Init ==
    /\ serverVersion = [s \in Servers |-> "old"]
    /\ serverStatus = [s \in Servers |-> "active"]
    /\ lbPool = Servers
    /\ pendingUpdate = "none"
    /\ updateRequested = FALSE
    /\ updateComplete = FALSE
    /\ coordState = "idle"
    /\ toUpdate = Servers
    /\ pc = [p \in {"coordinator"} \cup Servers |-> 
                IF p = "coordinator" THEN "coord_idle" ELSE "server_idle"]

\* Availability invariant: at least one server is always in the load balancer pool
\* (as long as we haven't finished and have active servers)
AvailabilityInvariant ==
    coordState # "done" => lbPool # {}

\* Safety: never remove last server from pool while deployment in progress
SafeDeployment ==
    (toUpdate # {} /\ pendingUpdate # "none") => 
        Cardinality(lbPool) >= 1

\* ----- Coordinator Process Actions -----

\* Coordinator starts the deployment process
CoordStart ==
    /\ pc["coordinator"] = "coord_idle"
    /\ toUpdate # {}
    /\ pc' = [pc EXCEPT !["coordinator"] = "coord_select"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, pendingUpdate, 
                   updateRequested, updateComplete, coordState, toUpdate>>

\* Coordinator selects next server to update
CoordSelect ==
    /\ pc["coordinator"] = "coord_select"
    /\ toUpdate # {}
    /\ \E s \in toUpdate:
        /\ pendingUpdate' = s
        /\ coordState' = "removing"
        /\ pc' = [pc EXCEPT !["coordinator"] = "coord_remove"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, updateRequested, 
                   updateComplete, toUpdate>>

\* Coordinator removes server from load balancer
CoordRemove ==
    /\ pc["coordinator"] = "coord_remove"
    /\ pendingUpdate # "none"
    /\ Cardinality(lbPool) > 1  \* Ensure we keep at least one server
    /\ lbPool' = lbPool \ {pendingUpdate}
    /\ serverStatus' = [serverStatus EXCEPT ![pendingUpdate] = "draining"]
    /\ pc' = [pc EXCEPT !["coordinator"] = "coord_request"]
    /\ UNCHANGED <<serverVersion, pendingUpdate, updateRequested, 
                   updateComplete, coordState, toUpdate>>

\* Coordinator requests update for the server
CoordRequestUpdate ==
    /\ pc["coordinator"] = "coord_request"
    /\ updateRequested' = TRUE
    /\ coordState' = "waiting"
    /\ pc' = [pc EXCEPT !["coordinator"] = "coord_wait"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, pendingUpdate, 
                   updateComplete, toUpdate>>

\* Coordinator waits for update completion
CoordWait ==
    /\ pc["coordinator"] = "coord_wait"
    /\ updateComplete = TRUE
    /\ coordState' = "restoring"
    /\ pc' = [pc EXCEPT !["coordinator"] = "coord_restore"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, pendingUpdate, 
                   updateRequested, updateComplete, toUpdate>>

\* Coordinator restores server to load balancer
CoordRestore ==
    /\ pc["coordinator"] = "coord_restore"
    /\ pendingUpdate # "none"
    /\ lbPool' = lbPool \cup {pendingUpdate}
    /\ serverStatus' = [serverStatus EXCEPT ![pendingUpdate] = "active"]
    /\ toUpdate' = toUpdate \ {pendingUpdate}
    /\ updateRequested' = FALSE
    /\ updateComplete' = FALSE
    /\ pendingUpdate' = "none"
    /\ coordState' = "idle"
    /\ pc' = [pc EXCEPT !["coordinator"] = 
                IF toUpdate' = {} THEN "coord_done" ELSE "coord_select"]
    /\ UNCHANGED <<serverVersion>>

\* Coordinator finishes when all servers updated
CoordDone ==
    /\ pc["coordinator"] = "coord_done"
    /\ coordState' = "done"
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, pendingUpdate, 
                   updateRequested, updateComplete, toUpdate, pc>>

\* ----- Server Update Process Actions -----

\* Server starts updating when requested
ServerStartUpdate(s) ==
    /\ pc[s] = "server_idle"
    /\ pendingUpdate = s
    /\ updateRequested = TRUE
    /\ serverStatus' = [serverStatus EXCEPT ![s] = "updating"]
    /\ pc' = [pc EXCEPT ![s] = "server_updating"]
    /\ UNCHANGED <<serverVersion, lbPool, pendingUpdate, updateRequested, 
                   updateComplete, coordState, toUpdate>>

\* Server completes the update
ServerCompleteUpdate(s) ==
    /\ pc[s] = "server_updating"
    /\ serverVersion' = [serverVersion EXCEPT ![s] = "new"]
    /\ serverStatus' = [serverStatus EXCEPT ![s] = "ready"]
    /\ updateComplete' = TRUE
    /\ pc' = [pc EXCEPT ![s] = "server_done"]
    /\ UNCHANGED <<lbPool, pendingUpdate, updateRequested, coordState, toUpdate>>

\* Server resets to idle after being restored
ServerReset(s) ==
    /\ pc[s] = "server_done"
    /\ serverStatus[s] = "active"  \* Wait until coordinator restores it
    /\ pc' = [pc EXCEPT ![s] = "server_idle"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, pendingUpdate, 
                   updateRequested, updateComplete, coordState, toUpdate>>

\* Combined server action
ServerAction(s) ==
    \/ ServerStartUpdate(s)
    \/ ServerCompleteUpdate(s)
    \/ ServerReset(s)

\* ----- Next State Relation -----

CoordinatorAction ==
    \/ CoordStart
    \/ CoordSelect
    \/ CoordRemove
    \/ CoordRequestUpdate
    \/ CoordWait
    \/ CoordRestore
    \/ CoordDone

Next ==
    \/ CoordinatorAction
    \/ \E s \in Servers: ServerAction(s)

\* ----- Fairness Conditions -----

\* Weak fairness for coordinator
CoordinatorFairness ==
    /\ WF_vars(CoordStart)
    /\ WF_vars(CoordSelect)
    /\ WF_vars(CoordRemove)
    /\ WF_vars(CoordRequestUpdate)
    /\ WF_vars(CoordWait)
    /\ WF_vars(CoordRestore)
    /\ WF_vars(CoordDone)

\* Weak fairness for each server
ServerFairness ==
    \A s \in Servers:
        /\ WF_vars(ServerStartUpdate(s))
        /\ WF_vars(ServerCompleteUpdate(s))
        /\ WF_vars(ServerReset(s))

Fairness == CoordinatorFairness /\ ServerFairness

\* ----- Specification -----

Spec == Init /\ [][Next]_vars /\ Fairness

\* ----- Liveness Properties -----

\* All servers eventually get updated
AllServersUpdated ==
    \A s \in Servers: serverVersion[s] = "new"

\* Termination: eventually all processes complete
Termination ==
    <>(coordState = "done" /\ AllServersUpdated)

\* Each server eventually gets the new version
EventualUpdate ==
    \A s \in Servers: <>(serverVersion[s] = "new")

\* The coordinator eventually finishes
CoordinatorTerminates ==
    <>(coordState = "done")

=============================================================================