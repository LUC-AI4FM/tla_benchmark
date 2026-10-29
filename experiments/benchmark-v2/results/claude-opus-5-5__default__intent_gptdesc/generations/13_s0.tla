------------------------------ MODULE RollingUpdate ------------------------------
EXTENDS FiniteSets

CONSTANTS
    Servers,        \* the set of identical servers behind the load balancer
    OldVersion,     \* the version all servers start with
    NewVersion,     \* the version all servers should end with
    Updating        \* distinguished intermediate (non-serving) state

ASSUME
    /\ Servers # {}
    /\ IsFiniteSet(Servers)
    /\ Cardinality(Servers) >= 2     \* zero downtime is impossible with one server
    /\ OldVersion # NewVersion
    /\ Updating # OldVersion
    /\ Updating # NewVersion

States == {OldVersion, NewVersion, Updating}

VARIABLES
    version,    \* version[s] : current version state of server s
    lb,         \* set of servers currently receiving traffic from the load balancer
    triggered,  \* servers the orchestrator has allowed/triggered to update
    orch        \* orchestrator phase: "idle", "active", or "done"

vars == <<version, lb, triggered, orch>>

-----------------------------------------------------------------------------
\* Helper definitions

OutOfLB == Servers \ lb

Serving(s) == version[s] \in {OldVersion, NewVersion}

AllUpdated == \A s \in Servers : version[s] = NewVersion

-----------------------------------------------------------------------------
TypeOK ==
    /\ version \in [Servers -> States]
    /\ lb \subseteq Servers
    /\ triggered \subseteq Servers
    /\ orch \in {"idle", "active", "done"}

Init ==
    /\ version = [s \in Servers |-> OldVersion]
    /\ lb = Servers
    /\ triggered = {}
    /\ orch = "idle"

-----------------------------------------------------------------------------
\* Orchestrator actions

\* The orchestrator initiates the rolling update procedure.
Begin ==
    /\ orch = "idle"
    /\ orch' = "active"
    /\ UNCHANGED <<version, lb, triggered>>

\* Remove a nonempty batch of not-yet-updated servers from the load balancer.
\* Batch size and choice are left open, but at least one server must remain.
Remove(S) ==
    /\ orch = "active"
    /\ S # {}
    /\ S \subseteq {s \in lb : version[s] = OldVersion}
    /\ lb \ S # {}
    /\ lb' = lb \ S
    /\ UNCHANGED <<version, triggered, orch>>

\* Trigger the update on a server that has been removed from the load balancer.
Trigger(s) ==
    /\ orch = "active"
    /\ s \notin lb
    /\ s \notin triggered
    /\ version[s] = OldVersion
    /\ triggered' = triggered \cup {s}
    /\ UNCHANGED <<version, lb, orch>>

\* Return removed servers to service. The orchestrator must wait until every
\* removed server has finished updating. If the servers still in the load
\* balancer run the new version, the returned servers are simply added.
\* Otherwise (they run the old version), an atomic cut-over is performed:
\* the updated servers become the load-balanced set and the old-version
\* servers are taken out, so the load-balanced set stays version-homogeneous.
Return ==
    /\ orch = "active"
    /\ OutOfLB # {}
    /\ \A s \in OutOfLB : version[s] = NewVersion
    /\ lb' = IF \A s \in lb : version[s] = NewVersion
                THEN lb \cup OutOfLB
                ELSE OutOfLB
    /\ UNCHANGED <<version, triggered, orch>>

\* The procedure completes once every server is updated and in service.
Complete ==
    /\ orch = "active"
    /\ lb = Servers
    /\ AllUpdated
    /\ orch' = "done"
    /\ UNCHANGED <<version, lb, triggered>>

-----------------------------------------------------------------------------
\* Server actions

\* A server starts updating once allowed (triggered and out of the LB).
StartUpdate(s) ==
    /\ s \in triggered
    /\ s \notin lb
    /\ version[s] = OldVersion
    /\ version' = [version EXCEPT ![s] = Updating]
    /\ UNCHANGED <<lb, triggered, orch>>

\* A server finishes updating and marks itself as updated.
FinishUpdate(s) ==
    /\ version[s] = Updating
    /\ version' = [version EXCEPT ![s] = NewVersion]
    /\ triggered' = triggered \ {s}
    /\ UNCHANGED <<lb, orch>>

\* Terminal stuttering once the procedure is done (avoids spurious deadlock).
Done ==
    /\ orch = "done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ Begin
    \/ \E S \in SUBSET Servers : Remove(S)
    \/ \E s \in Servers : Trigger(s)
    \/ \E s \in Servers : StartUpdate(s)
    \/ \E s \in Servers : FinishUpdate(s)
    \/ Return
    \/ Complete
    \/ Done

Fairness ==
    /\ WF_vars(Begin)
    /\ WF_vars(\E S \in SUBSET Servers : Remove(S))
    /\ \A s \in Servers : WF_vars(Trigger(s))
    /\ \A s \in Servers : WF_vars(StartUpdate(s))
    /\ \A s \in Servers : WF_vars(FinishUpdate(s))
    /\ WF_vars(Return)
    /\ WF_vars(Complete)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* The load-balanced set is version-homogeneous.
VersionHomogeneous ==
    \A s, t \in lb : version[s] = version[t]

\* No server in the intermediate state ever receives traffic.
NoUpdatingInLB ==
    \A s \in lb : version[s] # Updating

\* Zero downtime: the load-balanced set is never empty and always contains
\* at least one server able to serve requests.
ZeroDowntime ==
    /\ lb # {}
    /\ \E s \in lb : Serving(s)

\* Updates only happen on servers removed from the load balancer.
UpdatesOnlyOutOfLB ==
    \A s \in Servers : version[s] = Updating => s \notin lb

SafetyInvariant ==
    /\ TypeOK
    /\ VersionHomogeneous
    /\ NoUpdatingInLB
    /\ ZeroDowntime
    /\ UpdatesOnlyOutOfLB

\* The orchestrator only puts a server (back) into service once it has
\* finished updating.
ReturnOnlyWhenUpdated ==
    [][\A s \in Servers :
          (s \notin lb /\ s \in lb') => version[s] = NewVersion]_vars

\* Versions never move backwards.
NoDowngrade ==
    [][\A s \in Servers :
          /\ version[s] = NewVersion => version'[s] = NewVersion
          /\ version[s] = Updating => version'[s] \in {Updating, NewVersion}]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* Every server that starts updating eventually finishes.
UpdateFinishes ==
    \A s \in Servers : (version[s] = Updating) ~> (version[s] = NewVersion)

\* Once initiated, the procedure eventually completes with all servers
\* updated and back in service.
UpdateCompletes ==
    (orch = "active") ~> (orch = "done" /\ AllUpdated /\ lb = Servers)

\* The procedure eventually terminates.
Termination == <>(orch = "done")

\* Eventually all servers are permanently on the new version.
EventuallyAllUpdated == <>[]AllUpdated

=============================================================================