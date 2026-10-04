---------------------------- MODULE RollingUpdate ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Servers,        \* The set of all servers in the cluster
    OldVersion,     \* Representation of the old version
    NewVersion,     \* Representation of the new version
    Updating        \* Distinguished intermediate state during update

VARIABLES
    serverState,    \* Function: Server -> {OldVersion, Updating, NewVersion}
    loadBalanced    \* Set of servers currently in the load balancer pool

vars == <<serverState, loadBalanced>>

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ serverState \in [Servers -> {OldVersion, Updating, NewVersion}]
    /\ loadBalanced \subseteq Servers

-----------------------------------------------------------------------------
(* Initial state: all servers at old version and in load balancer *)
Init ==
    /\ serverState = [s \in Servers |-> OldVersion]
    /\ loadBalanced = Servers

-----------------------------------------------------------------------------
(* Helper predicates *)

\* A server is in a serving state (not updating)
IsServing(s) == serverState[s] \in {OldVersion, NewVersion}

\* The set of servers currently serving traffic
ServingServers == {s \in loadBalanced : IsServing(s)}

\* Get the version of serving servers (assumes homogeneity)
ServingVersions == {serverState[s] : s \in ServingServers}

\* Check if a server can be safely added back to load balancer
\* It must be serving and version-compatible with current serving servers
CanAddToLB(s) ==
    /\ IsServing(s)
    /\ \/ ServingServers = {}
       \/ serverState[s] \in ServingVersions

-----------------------------------------------------------------------------
(* Orchestrator Actions *)

\* Remove a subset of servers from load balancer for updating
\* Must leave at least one serving server in the load balancer
RemoveForUpdate(subset) ==
    /\ subset # {}
    /\ subset \subseteq loadBalanced
    /\ \A s \in subset : serverState[s] = OldVersion
    \* Ensure at least one serving server remains
    /\ Cardinality(loadBalanced \ subset) >= 1
    /\ \E s \in (loadBalanced \ subset) : IsServing(s)
    /\ loadBalanced' = loadBalanced \ subset
    /\ UNCHANGED serverState

\* Return updated servers to the load balancer
\* Only return servers that are done updating and version-compatible
ReturnToService(subset) ==
    /\ subset # {}
    /\ subset \subseteq (Servers \ loadBalanced)
    /\ \A s \in subset : serverState[s] = NewVersion
    \* Check version compatibility with current serving set
    /\ \/ ServingServers = {}
       \/ \A s \in ServingServers : serverState[s] = NewVersion
    /\ loadBalanced' = loadBalanced \cup subset
    /\ UNCHANGED serverState

-----------------------------------------------------------------------------
(* Server Actions *)

\* A server starts updating (only if removed from load balancer)
StartUpdate(s) ==
    /\ s \notin loadBalanced
    /\ serverState[s] = OldVersion
    /\ serverState' = [serverState EXCEPT ![s] = Updating]
    /\ UNCHANGED loadBalanced

\* A server finishes updating
FinishUpdate(s) ==
    /\ serverState[s] = Updating
    /\ serverState' = [serverState EXCEPT ![s] = NewVersion]
    /\ UNCHANGED loadBalanced

-----------------------------------------------------------------------------
(* Combined Next State Relation *)

OrchestratorAction ==
    \/ \E subset \in (SUBSET Servers \ {{}}) : RemoveForUpdate(subset)
    \/ \E subset \in (SUBSET Servers \ {{}}) : ReturnToService(subset)

ServerAction ==
    \E s \in Servers :
        \/ StartUpdate(s)
        \/ FinishUpdate(s)

Next ==
    \/ OrchestratorAction
    \/ ServerAction

-----------------------------------------------------------------------------
(* Fairness Conditions *)

\* Weak fairness on server update actions ensures updates eventually complete
\* Strong fairness on orchestrator ensures progress when possible
Fairness ==
    /\ \A s \in Servers : WF_vars(StartUpdate(s))
    /\ \A s \in Servers : WF_vars(FinishUpdate(s))
    /\ \A subset \in (SUBSET Servers \ {{}}) : SF_vars(RemoveForUpdate(subset))
    /\ \A subset \in (SUBSET Servers \ {{}}) : SF_vars(ReturnToService(subset))

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Version homogeneity: all serving servers must be at the same version
VersionHomogeneity ==
    \A s1, s2 \in ServingServers : serverState[s1] = serverState[s2]

\* Zero downtime: there is always at least one server serving
ZeroDowntime ==
    ServingServers # {}

\* Servers in load balancer must not be in updating state
NoUpdatingInLB ==
    \A s \in loadBalanced : serverState[s] # Updating

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ VersionHomogeneity
    /\ ZeroDowntime
    /\ NoUpdatingInLB

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* All servers eventually reach the new version
AllUpdated ==
    \A s \in Servers : serverState[s] = NewVersion

\* All servers eventually return to the load balancer with new version
AllServing ==
    loadBalanced = Servers

\* The update eventually completes: all servers updated and back in service
EventualCompletion ==
    <>(AllUpdated /\ AllServing)

\* If a server starts updating, it eventually finishes
UpdatesComplete ==
    \A s \in Servers :
        (serverState[s] = Updating) ~> (serverState[s] = NewVersion)

\* If a server is removed from LB, it eventually returns (with new version)
RemovedServersReturn ==
    \A s \in Servers :
        (s \notin loadBalanced) ~> (s \in loadBalanced)

-----------------------------------------------------------------------------
(* Invariants for model checking *)

\* This can be used to verify the model finds valid behaviors
NotAllUpdated == ~AllUpdated

=============================================================================