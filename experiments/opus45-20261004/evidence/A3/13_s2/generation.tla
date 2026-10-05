------------------------------ MODULE RollingDeployment ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Servers

VARIABLES
    serverVersion,      \* serverVersion[s] \in {"old", "new"} - current software version
    serverInLB,         \* serverInLB[s] \in BOOLEAN - whether server is in load balancer
    serverUpdating,     \* serverUpdating[s] \in BOOLEAN - whether server is being updated
    coordState,         \* State of coordinator: "idle", "removing", "waiting", "restoring", "done"
    currentServer,      \* Server currently being processed by coordinator (or a dummy value)
    toUpdate,           \* Set of servers still to be updated
    pc_coord,           \* Program counter for coordinator
    pc_server           \* pc_server[s] - program counter for each server update process

vars == <<serverVersion, serverInLB, serverUpdating, coordState, currentServer, toUpdate, pc_coord, pc_server>>

\* Type invariant
TypeOK ==
    /\ serverVersion \in [Servers -> {"old", "new"}]
    /\ serverInLB \in [Servers -> BOOLEAN]
    /\ serverUpdating \in [Servers -> BOOLEAN]
    /\ coordState \in {"idle", "removing", "waiting", "restoring", "done"}
    /\ (currentServer \in Servers \/ currentServer = "none")
    /\ toUpdate \subseteq Servers
    /\ pc_coord \in {"start", "selectServer", "removeFromLB", "triggerUpdate", "waitUpdate", "addToLB", "done"}
    /\ pc_server \in [Servers -> {"idle", "updating", "done"}]

\* Safety: At least one server must always be in the load balancer (availability)
AtLeastOneServerInLB ==
    \E s \in Servers : serverInLB[s]

\* Safety: A server being updated should not be in the load balancer
UpdatingServerNotInLB ==
    \A s \in Servers : serverUpdating[s] => ~serverInLB[s]

\* Initialization
Init ==
    /\ serverVersion = [s \in Servers |-> "old"]
    /\ serverInLB = [s \in Servers |-> TRUE]
    /\ serverUpdating = [s \in Servers |-> FALSE]
    /\ coordState = "idle"
    /\ currentServer = "none"
    /\ toUpdate = Servers
    /\ pc_coord = "start"
    /\ pc_server = [s \in Servers |-> "idle"]

\* Coordinator actions

CoordStart ==
    /\ pc_coord = "start"
    /\ pc_coord' = "selectServer"
    /\ coordState' = "idle"
    /\ UNCHANGED <<serverVersion, serverInLB, serverUpdating, currentServer, toUpdate, pc_server>>

CoordSelectServer ==
    /\ pc_coord = "selectServer"
    /\ IF toUpdate = {}
       THEN /\ pc_coord' = "done"
            /\ coordState' = "done"
            /\ UNCHANGED <<currentServer, toUpdate>>
       ELSE \E s \in toUpdate :
            /\ currentServer' = s
            /\ toUpdate' = toUpdate \ {s}
            /\ pc_coord' = "removeFromLB"
            /\ coordState' = "removing"
    /\ UNCHANGED <<serverVersion, serverInLB, serverUpdating, pc_server>>

CoordRemoveFromLB ==
    /\ pc_coord = "removeFromLB"
    /\ currentServer # "none"
    \* Only remove if there's at least one other server in LB to maintain availability
    /\ Cardinality({s \in Servers : serverInLB[s]}) > 1
    /\ serverInLB' = [serverInLB EXCEPT ![currentServer] = FALSE]
    /\ pc_coord' = "triggerUpdate"
    /\ coordState' = "removing"
    /\ UNCHANGED <<serverVersion, serverUpdating, currentServer, toUpdate, pc_server>>

CoordTriggerUpdate ==
    /\ pc_coord = "triggerUpdate"
    /\ currentServer # "none"
    /\ serverUpdating' = [serverUpdating EXCEPT ![currentServer] = TRUE]
    /\ pc_server' = [pc_server EXCEPT ![currentServer] = "updating"]
    /\ pc_coord' = "waitUpdate"
    /\ coordState' = "waiting"
    /\ UNCHANGED <<serverVersion, serverInLB, currentServer, toUpdate>>

CoordWaitUpdate ==
    /\ pc_coord = "waitUpdate"
    /\ currentServer # "none"
    /\ pc_server[currentServer] = "done"  \* Wait for server update to complete
    /\ pc_coord' = "addToLB"
    /\ coordState' = "restoring"
    /\ UNCHANGED <<serverVersion, serverInLB, serverUpdating, currentServer, toUpdate, pc_server>>

CoordAddToLB ==
    /\ pc_coord = "addToLB"
    /\ currentServer # "none"
    /\ serverInLB' = [serverInLB EXCEPT ![currentServer] = TRUE]
    /\ pc_coord' = "selectServer"
    /\ coordState' = "idle"
    /\ currentServer' = "none"
    /\ UNCHANGED <<serverVersion, serverUpdating, toUpdate, pc_server>>

CoordDone ==
    /\ pc_coord = "done"
    /\ UNCHANGED vars

\* Server update process actions

ServerUpdate(s) ==
    /\ pc_server[s] = "updating"
    /\ serverUpdating[s] = TRUE
    /\ serverVersion' = [serverVersion EXCEPT ![s] = "new"]
    /\ serverUpdating' = [serverUpdating EXCEPT ![s] = FALSE]
    /\ pc_server' = [pc_server EXCEPT ![s] = "done"]
    /\ UNCHANGED <<serverInLB, coordState, currentServer, toUpdate, pc_coord>>

ServerIdle(s) ==
    /\ pc_server[s] = "idle"
    /\ UNCHANGED vars

ServerDone(s) ==
    /\ pc_server[s] = "done"
    /\ UNCHANGED vars

\* Combined server action
ServerAction(s) ==
    \/ ServerUpdate(s)
    \/ ServerIdle(s)
    \/ ServerDone(s)

\* Coordinator combined action
CoordinatorAction ==
    \/ CoordStart
    \/ CoordSelectServer
    \/ CoordRemoveFromLB
    \/ CoordTriggerUpdate
    \/ CoordWaitUpdate
    \/ CoordAddToLB
    \/ CoordDone

\* Next state relation
Next ==
    \/ CoordinatorAction
    \/ \E s \in Servers : ServerAction(s)

\* Fairness conditions
CoordinatorFairness ==
    /\ WF_vars(CoordStart)
    /\ WF_vars(CoordSelectServer)
    /\ WF_vars(CoordRemoveFromLB)
    /\ WF_vars(CoordTriggerUpdate)
    /\ WF_vars(CoordWaitUpdate)
    /\ WF_vars(CoordAddToLB)

ServerFairness ==
    \A s \in Servers : WF_vars(ServerUpdate(s))

Fairness == CoordinatorFairness /\ ServerFairness

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination: All processes eventually complete
AllServersUpdated ==
    \A s \in Servers : serverVersion[s] = "new"

CoordinatorDone ==
    pc_coord = "done"

Termination == <>(AllServersUpdated /\ CoordinatorDone)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ AtLeastOneServerInLB
    /\ UpdatingServerNotInLB

\* Progress property: If a server starts updating, it eventually completes
UpdateProgress ==
    \A s \in Servers : (pc_server[s] = "updating") ~> (pc_server[s] = "done")

=============================================================================