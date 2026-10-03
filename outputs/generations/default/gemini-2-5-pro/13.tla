---- MODULE RollingDeployment ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Servers
ASSUME Servers /= {}

VARIABLES server_state, in_service, coord_pc, selected_server

vars == <<server_state, in_service, coord_pc, selected_server>>

ServerStates == {"pending_update", "updating", "up_to_date"}
CoordStates == {"idle", "selecting", "draining", "waiting", "restoring", "done"}

TypeOK ==
    /\ server_state \in [Servers -> ServerStates]
    /\ in_service \subseteq Servers
    /\ coord_pc \in CoordStates
    /\ selected_server \in Servers \cup {"None"}

\* The set of servers that still need to be updated.
PendingServers == {s \in Servers : server_state[s] = "pending_update"}

\* -- Actions --

\* The coordinator process selects a server to update.
Coord_Select ==
    /\ coord_pc = "idle"
    /\ PendingServers /= {}  \* There is work to do
    /\ \E s \in PendingServers:
        /\ selected_server' = s
        /\ coord_pc' = "selecting"
    /\ UNCHANGED <<server_state, in_service>>

\* The coordinator removes the selected server from the load balancer.
Coord_Drain ==
    /\ coord_pc = "selecting"
    /\ in_service' = in_service \ {selected_server}
    /\ coord_pc' = "draining"
    /\ UNCHANGED <<server_state, selected_server>>

\* The coordinator triggers the update on the server.
Coord_TriggerUpdate ==
    /\ coord_pc = "draining"
    /\ server_state' = [server_state EXCEPT ![selected_server] = "updating"]
    /\ coord_pc' = "waiting"
    /\ UNCHANGED <<in_service, selected_server>>

\* The coordinator waits for the server to report completion.
Coord_Wait ==
    /\ coord_pc = "waiting"
    /\ server_state[selected_server] = "up_to_date"
    /\ coord_pc' = "restoring"
    /\ UNCHANGED <<server_state, in_service, selected_server>>

\* The coordinator adds the server back to the load balancer.
Coord_Restore ==
    /\ coord_pc = "restoring"
    /\ in_service' = in_service \cup {selected_server}
    /\ coord_pc' = "idle"
    /\ selected_server' = "None"
    /\ UNCHANGED <<server_state>>

\* The coordinator detects all servers are updated and finishes.
Coord_Finish ==
    /\ coord_pc = "idle"
    /\ PendingServers = {}
    /\ coord_pc' = "done"
    /\ UNCHANGED <<server_state, in_service, selected_server>>

Coordinator ==
    \/ Coord_Select
    \/ Coord_Drain
    \/ Coord_TriggerUpdate
    \/ Coord_Wait
    \/ Coord_Restore
    \/ Coord_Finish

\* An individual server completes its update.
ServerUpdate(s) ==
    /\ server_state[s] = "updating"
    /\ server_state' = [server_state EXCEPT ![s] = "up_to_date"]
    /\ UNCHANGED <<in_service, coord_pc, selected_server>>

\* -- Specification --

Init ==
    /\ server_state = [s \in Servers |-> "pending_update"]
    /\ in_service = Servers
    /\ coord_pc = "idle"
    /\ selected_server = "None"

Next ==
    \/ Coordinator
    \/ \E s \in Servers: ServerUpdate(s)

Fairness == WF_vars(Coordinator) /\ \A s \in Servers: WF_vars(ServerUpdate(s))

Spec == Init /\ [][Next]_vars /\ Fairness

\* -- Properties --

\* Safety: At least one server is in service if we have more than one server.
Availability == Cardinality(Servers) > 1 => in_service /= {}

\* Liveness: The deployment eventually completes.
Termination == <> (coord_pc = "done")

=============================================================================