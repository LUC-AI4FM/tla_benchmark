---------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Servers

VARIABLES 
    serverState,      \* Function: server -> {"running", "updating", "updated"}
    lbState,          \* Function: server -> {"in_lb", "out_of_lb"}
    coordState,       \* Coordinator state
    currentServer,    \* Server currently being processed by coordinator
    serverPC,         \* PC for each server's update process
    coordPC,          \* PC for coordinator process
    pendingServers    \* Servers remaining to be updated

vars == <<serverState, lbState, coordState, currentServer, serverPC, coordPC, pendingServers>>

\* Type invariant
TypeOK ==
    /\ serverState \in [Servers -> {"running", "updating", "updated"}]
    /\ lbState \in [Servers -> {"in_lb", "out_of_lb"}]
    /\ coordState \in {"idle", "removing", "waiting", "restoring", "done"}
    /\ currentServer \in Servers \cup {CHOOSE x : x \notin Servers}
    /\ serverPC \in [Servers -> {"idle", "updating", "done"}]
    /\ coordPC \in {"start", "select", "remove", "trigger", "wait", "restore", "next", "done"}
    /\ pendingServers \subseteq Servers

NoServer == CHOOSE x : x \notin Servers

\* Initial state
Init ==
    /\ serverState = [s \in Servers |-> "running"]
    /\ lbState = [s \in Servers |-> "in_lb"]
    /\ coordState = "idle"
    /\ currentServer = NoServer
    /\ serverPC = [s \in Servers |-> "idle"]
    /\ coordPC = "start"
    /\ pendingServers = Servers

\* Server update process - performs the actual update when triggered
ServerUpdate(s) ==
    /\ serverPC[s] = "updating"
    /\ serverState[s] = "updating"
    /\ serverState' = [serverState EXCEPT ![s] = "updated"]
    /\ serverPC' = [serverPC EXCEPT ![s] = "done"]
    /\ UNCHANGED <<lbState, coordState, currentServer, coordPC, pendingServers>>

\* Coordinator: Start the deployment process
CoordStart ==
    /\ coordPC = "start"
    /\ coordState = "idle"
    /\ pendingServers # {}
    /\ coordPC' = "select"
    /\ UNCHANGED <<serverState, lbState, coordState, currentServer, serverPC, pendingServers>>

\* Coordinator: Select next server to update
CoordSelect ==
    /\ coordPC = "select"
    /\ pendingServers # {}
    /\ \E s \in pendingServers:
        /\ currentServer' = s
        /\ coordPC' = "remove"
        /\ coordState' = "removing"
    /\ UNCHANGED <<serverState, lbState, serverPC, pendingServers>>

\* Coordinator: Remove server from load balancer
CoordRemove ==
    /\ coordPC = "remove"
    /\ coordState = "removing"
    /\ currentServer # NoServer
    /\ lbState' = [lbState EXCEPT ![currentServer] = "out_of_lb"]
    /\ coordPC' = "trigger"
    /\ UNCHANGED <<serverState, coordState, currentServer, serverPC, pendingServers>>

\* Coordinator: Trigger update on the server
CoordTrigger ==
    /\ coordPC = "trigger"
    /\ currentServer # NoServer
    /\ serverState' = [serverState EXCEPT ![currentServer] = "updating"]
    /\ serverPC' = [serverPC EXCEPT ![currentServer] = "updating"]
    /\ coordState' = "waiting"
    /\ coordPC' = "wait"
    /\ UNCHANGED <<lbState, currentServer, pendingServers>>

\* Coordinator: Wait for server update to complete
CoordWait ==
    /\ coordPC = "wait"
    /\ coordState = "waiting"
    /\ currentServer # NoServer
    /\ serverState[currentServer] = "updated"
    /\ serverPC[currentServer] = "done"
    /\ coordState' = "restoring"
    /\ coordPC' = "restore"
    /\ UNCHANGED <<serverState, lbState, currentServer, serverPC, pendingServers>>

\* Coordinator: Restore server to load balancer
CoordRestore ==
    /\ coordPC = "restore"
    /\ coordState = "restoring"
    /\ currentServer # NoServer
    /\ lbState' = [lbState EXCEPT ![currentServer] = "in_lb"]
    /\ coordPC' = "next"
    /\ UNCHANGED <<serverState, coordState, currentServer, serverPC, pendingServers>>

\* Coordinator: Move to next server
CoordNext ==
    /\ coordPC = "next"
    /\ currentServer # NoServer
    /\ pendingServers' = pendingServers \ {currentServer}
    /\ coordState' = "idle"
    /\ currentServer' = NoServer
    /\ IF pendingServers \ {currentServer} = {}
       THEN coordPC' = "done"
       ELSE coordPC' = "select"
    /\ UNCHANGED <<serverState, lbState, serverPC>>

\* Coordinator: Done state (stutter)
CoordDone ==
    /\ coordPC = "done"
    /\ coordState' = "done"
    /\ UNCHANGED <<serverState, lbState, currentServer, serverPC, coordPC, pendingServers>>

\* Combined coordinator action
CoordAction ==
    \/ CoordStart
    \/ CoordSelect
    \/ CoordRemove
    \/ CoordTrigger
    \/ CoordWait
    \/ CoordRestore
    \/ CoordNext
    \/ CoordDone

\* Combined server action
ServerAction ==
    \E s \in Servers: ServerUpdate(s)

\* Next state relation
Next ==
    \/ CoordAction
    \/ ServerAction

\* Fairness conditions
CoordFairness ==
    /\ WF_vars(CoordStart)
    /\ WF_vars(CoordSelect)
    /\ WF_vars(CoordRemove)
    /\ WF_vars(CoordTrigger)
    /\ WF_vars(CoordWait)
    /\ WF_vars(CoordRestore)
    /\ WF_vars(CoordNext)
    /\ WF_vars(CoordDone)

ServerFairness ==
    \A s \in Servers: WF_vars(ServerUpdate(s))

Fairness == CoordFairness /\ ServerFairness

\* The main specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination property
Terminated ==
    /\ coordPC = "done"
    /\ coordState = "done"
    /\ \A s \in Servers: serverPC[s] = "done"
    /\ \A s \in Servers: serverState[s] = "updated"

Termination == <>(Terminated)

\* Availability invariant: at least one server is always in the load balancer
Availability == \E s \in Servers: lbState[s] = "in_lb"

=============================================================================