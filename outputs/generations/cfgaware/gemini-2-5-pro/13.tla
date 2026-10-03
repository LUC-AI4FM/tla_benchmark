---- MODULE RollingDeployment ----
EXTENDS TLC, FiniteSets

CONSTANT Server, InitialVersion, NewVersion

VARIABLES pc, version, in_service, updating, target_server

vars == <<pc, version, in_service, updating, target_server>>

Processes == {"coordinator"} \cup Server

Init ==
    /\ pc = [ self \in Processes |->
                IF self = "coordinator" THEN "Coord_Select"
                ELSE "S_Idle" ]
    /\ version = [s \in Server |-> InitialVersion]
    /\ in_service = [s \in Server |-> TRUE]
    /\ updating = [s \in Server |-> FALSE]
    /\ target_server \in Server

(* Coordinator process actions *)
Coord_StartUpdate ==
    /\ pc["coordinator"] = "Coord_Select"
    /\ \E s \in Server: version[s] = InitialVersion
    /\ \E s \in {t \in Server : version[t] = InitialVersion}:
        /\ target_server' = s
        /\ in_service' = [in_service EXCEPT ![s] = FALSE]
        /\ updating' = [updating EXCEPT ![s] = TRUE]
        /\ pc' = [pc EXCEPT !["coordinator"] = "Coord_Wait"]
    /\ UNCHANGED <<version>>

Coord_EndUpdate ==
    /\ pc["coordinator"] = "Coord_Wait"
    /\ updating[target_server] = FALSE
    /\ in_service' = [in_service EXCEPT ![target_server] = TRUE]
    /\ pc' = [pc EXCEPT !["coordinator"] = "Coord_Select"]
    /\ UNCHANGED <<version, updating, target_server>>

Coord_Done ==
    /\ pc["coordinator"] = "Coord_Select"
    /\ \A s \in Server: version[s] = NewVersion
    /\ pc' = [pc EXCEPT !["coordinator"] = "Done"]
    /\ UNCHANGED <<version, in_service, updating, target_server>>

Coordinator ==
    \/ Coord_StartUpdate
    \/ Coord_EndUpdate
    \/ Coord_Done

(* Per-server update process actions *)
S_Update(s) ==
    /\ pc[s] = "S_Idle"
    /\ updating[s] = TRUE
    /\ version' = [version EXCEPT ![s] = NewVersion]
    /\ pc' = [pc EXCEPT ![s] = "S_Finish"]
    /\ UNCHANGED <<in_service, updating, target_server>>

S_Finish(s) ==
    /\ pc[s] = "S_Finish"
    /\ updating' = [updating EXCEPT ![s] = FALSE]
    /\ pc' = [pc EXCEPT ![s] = "Done"]
    /\ UNCHANGED <<version, in_service, target_server>>

Update(s) == S_Update(s) \/ S_Finish(s)

Next ==
    \/ Coordinator
    \/ \E s \in Server: Update(s)

Spec == Init /\ [][Next]_vars /\ WF_vars(Coordinator) /\ \A s \in Server: WF_vars(Update(s))

====================