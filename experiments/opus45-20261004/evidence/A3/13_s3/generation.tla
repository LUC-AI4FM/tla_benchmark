---- MODULE RollingDeployment ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Servers

ASSUME Servers # {}

(* Server states *)
ServerStates == {"running", "updating", "updated"}

(* Coordinator states *)
CoordinatorStates == {"idle", "removing", "triggering", "waiting", "restoring", "done"}

VARIABLES
    serverState,        \* Function: Server -> ServerState
    loadBalancer,       \* Set of servers currently in the load balancer
    toUpdate,           \* Set of servers that still need to be updated
    currentServer,      \* The server currently being updated (or NONE)
    coordinatorState,   \* State of the coordinator process
    updateRequested,    \* Flag indicating coordinator requested an update
    pc_coord,           \* Program counter for coordinator
    pc_server           \* Function: Server -> program counter for each server update process

vars == <<serverState, loadBalancer, toUpdate, currentServer, coordinatorState, updateRequested, pc_coord, pc_server>>

NONE == CHOOSE x : x \notin Servers

(* Type invariant *)
TypeOK ==
    /\ serverState \in [Servers -> ServerStates]
    /\ loadBalancer \subseteq Servers
    /\ toUpdate \subseteq Servers
    /\ currentServer \in Servers \cup {NONE}
    /\ coordinatorState \in CoordinatorStates
    /\ updateRequested \in BOOLEAN
    /\ pc_coord \in {"start", "select", "remove", "trigger", "wait", "restore", "done"}
    /\ pc_server \in [Servers -> {"idle", "updating", "done"}]

(* Initialization *)
Init ==
    /\ serverState = [s \in Servers |-> "running"]
    /\ loadBalancer = Servers
    /\ toUpdate = Servers
    /\ currentServer = NONE
    /\ coordinatorState = "idle"
    /\ updateRequested = FALSE
    /\ pc_coord = "start"
    /\ pc_server = [s \in Servers |-> "idle"]

(* Coordinator actions *)

\* Start the deployment process
CoordStart ==
    /\ pc_coord = "start"
    /\ toUpdate # {}
    /\ pc_coord' = "select"
    /\ UNCHANGED <<serverState, loadBalancer, toUpdate, currentServer, coordinatorState, updateRequested, pc_server>>

\* Select next server to update
CoordSelect ==
    /\ pc_coord = "select"
    /\ toUpdate # {}
    /\ LET s == CHOOSE x \in toUpdate : TRUE
       IN currentServer' = s
    /\ coordinatorState' = "removing"
    /\ pc_coord' = "remove"
    /\ UNCHANGED <<serverState, loadBalancer, toUpdate, updateRequested, pc_server>>

\* Remove server from load balancer
CoordRemove ==
    /\ pc_coord = "remove"
    /\ currentServer # NONE
    /\ loadBalancer' = loadBalancer \ {currentServer}
    /\ coordinatorState' = "triggering"
    /\ pc_coord' = "trigger"
    /\ UNCHANGED <<serverState, toUpdate, currentServer, updateRequested, pc_server>>

\* Trigger update on the server
CoordTrigger ==
    /\ pc_coord = "trigger"
    /\ currentServer # NONE
    /\ updateRequested' = TRUE
    /\ coordinatorState' = "waiting"
    /\ pc_coord' = "wait"
    /\ UNCHANGED <<serverState, loadBalancer, toUpdate, currentServer, pc_server>>

\* Wait for update completion
CoordWait ==
    /\ pc_coord = "wait"
    /\ currentServer # NONE
    /\ serverState[currentServer] = "updated"
    /\ coordinatorState' = "restoring"
    /\ pc_coord' = "restore"
    /\ UNCHANGED <<serverState, loadBalancer, toUpdate, currentServer, updateRequested, pc_server>>

\* Restore server to load balancer
CoordRestore ==
    /\ pc_coord = "restore"
    /\ currentServer # NONE
    /\ loadBalancer' = loadBalancer \cup {currentServer}
    /\ toUpdate' = toUpdate \ {currentServer}
    /\ coordinatorState' = "idle"
    /\ currentServer' = NONE
    /\ updateRequested' = FALSE
    /\ pc_coord' = IF toUpdate' = {} THEN "done" ELSE "select"
    /\ UNCHANGED <<serverState, pc_server>>

\* Coordinator is done
CoordDone ==
    /\ pc_coord = "done"
    /\ coordinatorState' = "done"
    /\ UNCHANGED <<serverState, loadBalancer, toUpdate, currentServer, updateRequested, pc_coord, pc_server>>

\* Combined coordinator action
Coordinator ==
    \/ CoordStart
    \/ CoordSelect
    \/ CoordRemove
    \/ CoordTrigger
    \/ CoordWait
    \/ CoordRestore
    \/ CoordDone

(* Server update process actions *)

\* Server starts updating when requested by coordinator
ServerStartUpdate(s) ==
    /\ pc_server[s] = "idle"
    /\ currentServer = s
    /\ updateRequested = TRUE
    /\ serverState[s] = "running"
    /\ serverState' = [serverState EXCEPT ![s] = "updating"]
    /\ pc_server' = [pc_server EXCEPT ![s] = "updating"]
    /\ UNCHANGED <<loadBalancer, toUpdate, currentServer, coordinatorState, updateRequested, pc_coord>>

\* Server completes update
ServerCompleteUpdate(s) ==
    /\ pc_server[s] = "updating"
    /\ serverState[s] = "updating"
    /\ serverState' = [serverState EXCEPT ![s] = "updated"]
    /\ pc_server' = [pc_server EXCEPT ![s] = "done"]
    /\ UNCHANGED <<loadBalancer, toUpdate, currentServer, coordinatorState, updateRequested, pc_coord>>

\* Combined server action for a specific server
ServerUpdate(s) ==
    \/ ServerStartUpdate(s)
    \/ ServerCompleteUpdate(s)

\* All server actions
ServerActions ==
    \E s \in Servers : ServerUpdate(s)

(* Next state relation *)
Next ==
    \/ Coordinator
    \/ ServerActions

(* Fairness conditions *)
CoordFairness ==
    /\ WF_vars(CoordStart)
    /\ WF_vars(CoordSelect)
    /\ WF_vars(CoordRemove)
    /\ WF_vars(CoordTrigger)
    /\ WF_vars(CoordWait)
    /\ WF_vars(CoordRestore)
    /\ WF_vars(CoordDone)

ServerFairness ==
    \A s \in Servers :
        /\ WF_vars(ServerStartUpdate(s))
        /\ WF_vars(ServerCompleteUpdate(s))

Fairness == CoordFairness /\ ServerFairness

(* Specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety Invariants *)

\* At least one server is always available in the load balancer (availability)
Availability == loadBalancer # {}

\* A server being updated should not be in the load balancer
UpdateSafety ==
    \A s \in Servers : serverState[s] = "updating" => s \notin loadBalancer

\* At most one server is being updated at a time
SingleUpdate ==
    Cardinality({s \in Servers : serverState[s] = "updating"}) <= 1

(* Liveness Properties *)

\* All processes eventually terminate
Termination ==
    <>(pc_coord = "done" /\ \A s \in Servers : pc_server[s] = "done")

\* All servers are eventually updated
AllUpdated ==
    <>(\A s \in Servers : serverState[s] = "updated")

\* Eventually all servers are back in the load balancer with updated state
DeploymentComplete ==
    <>(loadBalancer = Servers /\ \A s \in Servers : serverState[s] = "updated")

====