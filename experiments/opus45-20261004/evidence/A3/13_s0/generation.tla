---- MODULE RollingDeployment ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Servers

ASSUME Servers # {} /\ IsFiniteSet(Servers)

VARIABLES 
    serverState,      \* Function: Server -> {"old", "updating", "new"}
    loadBalancer,     \* Set of servers currently in the load balancer
    coordState,       \* Coordinator state: "idle", "removing", "waiting", "restoring", "done"
    currentServer,    \* Server currently being updated (or NONE)
    toUpdate,         \* Set of servers still needing update
    pc_coord,         \* Program counter for coordinator
    pc_server         \* Function: Server -> program counter for each server updater

vars == <<serverState, loadBalancer, coordState, currentServer, toUpdate, pc_coord, pc_server>>

NONE == CHOOSE x : x \notin Servers

TypeOK ==
    /\ serverState \in [Servers -> {"old", "updating", "new"}]
    /\ loadBalancer \subseteq Servers
    /\ coordState \in {"idle", "removing", "waiting", "restoring", "done"}
    /\ (currentServer \in Servers) \/ (currentServer = NONE)
    /\ toUpdate \subseteq Servers
    /\ pc_coord \in {"start", "select", "remove", "trigger", "wait", "restore", "check", "done"}
    /\ pc_server \in [Servers -> {"idle", "updating", "done"}]

Init ==
    /\ serverState = [s \in Servers |-> "old"]
    /\ loadBalancer = Servers
    /\ coordState = "idle"
    /\ currentServer = NONE
    /\ toUpdate = Servers
    /\ pc_coord = "start"
    /\ pc_server = [s \in Servers |-> "idle"]

\* Coordinator selects next server to update
CoordSelect ==
    /\ pc_coord = "start" \/ pc_coord = "check"
    /\ toUpdate # {}
    /\ LET s == CHOOSE x \in toUpdate : TRUE
       IN /\ currentServer' = s
          /\ pc_coord' = "remove"
    /\ UNCHANGED <<serverState, loadBalancer, coordState, toUpdate, pc_server>>

\* Coordinator removes current server from load balancer
CoordRemove ==
    /\ pc_coord = "remove"
    /\ currentServer # NONE
    /\ loadBalancer' = loadBalancer \ {currentServer}
    /\ coordState' = "removing"
    /\ pc_coord' = "trigger"
    /\ UNCHANGED <<serverState, currentServer, toUpdate, pc_server>>

\* Coordinator triggers update on current server
CoordTrigger ==
    /\ pc_coord = "trigger"
    /\ currentServer # NONE
    /\ pc_server[currentServer] = "idle"
    /\ pc_server' = [pc_server EXCEPT ![currentServer] = "updating"]
    /\ serverState' = [serverState EXCEPT ![currentServer] = "updating"]
    /\ coordState' = "waiting"
    /\ pc_coord' = "wait"
    /\ UNCHANGED <<loadBalancer, currentServer, toUpdate>>

\* Coordinator waits for update to complete
CoordWait ==
    /\ pc_coord = "wait"
    /\ currentServer # NONE
    /\ pc_server[currentServer] = "done"
    /\ serverState[currentServer] = "new"
    /\ pc_coord' = "restore"
    /\ UNCHANGED <<serverState, loadBalancer, coordState, currentServer, toUpdate, pc_server>>

\* Coordinator restores server to load balancer
CoordRestore ==
    /\ pc_coord = "restore"
    /\ currentServer # NONE
    /\ loadBalancer' = loadBalancer \cup {currentServer}
    /\ toUpdate' = toUpdate \ {currentServer}
    /\ coordState' = "restoring"
    /\ pc_coord' = "check"
    /\ currentServer' = NONE
    /\ UNCHANGED <<serverState, pc_server>>

\* Coordinator checks if done
CoordCheckDone ==
    /\ pc_coord = "check"
    /\ toUpdate = {}
    /\ coordState' = "done"
    /\ pc_coord' = "done"
    /\ UNCHANGED <<serverState, loadBalancer, currentServer, toUpdate, pc_server>>

\* Server performs update
ServerUpdate(s) ==
    /\ pc_server[s] = "updating"
    /\ serverState[s] = "updating"
    /\ serverState' = [serverState EXCEPT ![s] = "new"]
    /\ pc_server' = [pc_server EXCEPT ![s] = "done"]
    /\ UNCHANGED <<loadBalancer, coordState, currentServer, toUpdate, pc_coord>>

\* Combined coordinator actions
CoordNext ==
    \/ CoordSelect
    \/ CoordRemove
    \/ CoordTrigger
    \/ CoordWait
    \/ CoordRestore
    \/ CoordCheckDone

\* Combined server actions
ServerNext ==
    \E s \in Servers : ServerUpdate(s)

Next ==
    \/ CoordNext
    \/ ServerNext

\* Fairness conditions
CoordFairness ==
    /\ WF_vars(CoordSelect)
    /\ WF_vars(CoordRemove)
    /\ WF_vars(CoordTrigger)
    /\ WF_vars(CoordWait)
    /\ WF_vars(CoordRestore)
    /\ WF_vars(CoordCheckDone)

ServerFairness ==
    \A s \in Servers : WF_vars(ServerUpdate(s))

Fairness == CoordFairness /\ ServerFairness

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: At least one server is always available in the load balancer
\* (availability preservation during deployment)
AvailabilityInvariant ==
    loadBalancer # {}

\* Safety invariant: A server being updated should not be in the load balancer
UpdateSafety ==
    \A s \in Servers : serverState[s] = "updating" => s \notin loadBalancer

\* Safety invariant: Only one server can be updating at a time
SingleUpdate ==
    Cardinality({s \in Servers : serverState[s] = "updating"}) <= 1

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ AvailabilityInvariant
    /\ UpdateSafety
    /\ SingleUpdate

\* Termination: All processes eventually complete
AllServersUpdated == \A s \in Servers : serverState[s] = "new"
CoordinatorDone == pc_coord = "done"
AllServerProcessesDone == \A s \in Servers : pc_server[s] = "done" \/ pc_server[s] = "idle"

Termination == <>(AllServersUpdated /\ CoordinatorDone)

\* Liveness: Every server eventually gets updated
EventualUpdate == \A s \in Servers : <>(serverState[s] = "new")

====