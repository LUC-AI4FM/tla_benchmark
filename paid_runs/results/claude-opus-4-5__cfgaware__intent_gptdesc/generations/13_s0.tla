---------------------------- MODULE RollingUpdate ----------------------------

CONSTANTS
    Servers,           \* The set of all servers in the cluster
    UpdatingState      \* Distinguished representation for "updating" intermediate state

VARIABLES
    version,           \* version[s] \in {"old", UpdatingState, "new"} - current version/state of server s
    loadBalanced       \* loadBalanced - set of servers currently in the load balancer

vars == <<version, loadBalanced>>

-----------------------------------------------------------------------------

\* Type invariant
TypeOK ==
    /\ version \in [Servers -> {"old", UpdatingState, "new"}]
    /\ loadBalanced \subseteq Servers

\* Initial state: all servers are on old version and in the load balancer
Init ==
    /\ version = [s \in Servers |-> "old"]
    /\ loadBalanced = Servers

-----------------------------------------------------------------------------

\* A server is in a servable state if it's not in the updating state
IsServable(s) == version[s] \in {"old", "new"}

\* Get the version of servable servers (excluding updating state)
ServableVersion(s) == version[s]

\* All servers currently serving traffic (in load balancer and servable)
ServingServers == {s \in loadBalanced : IsServable(s)}

\* Check if all serving servers have homogeneous versions
VersionHomogeneous ==
    \/ ServingServers = {}
    \/ \E v \in {"old", "new"} : \A s \in ServingServers : version[s] = v

-----------------------------------------------------------------------------

\* Orchestrator removes a non-empty subset of servers from load balancer
\* Constraint: must leave at least one servable server in the load balancer
RemoveFromLB(subset) ==
    /\ subset # {}
    /\ subset \subseteq loadBalanced
    \* Ensure at least one servable server remains
    /\ \E s \in (loadBalanced \ subset) : IsServable(s)
    \* Can only remove servers that are in old version (not yet updated)
    /\ \A s \in subset : version[s] = "old"
    /\ loadBalanced' = loadBalanced \ subset
    /\ UNCHANGED version

\* A server starts updating (must not be in load balancer)
StartUpdate(s) ==
    /\ s \notin loadBalanced
    /\ version[s] = "old"
    /\ version' = [version EXCEPT ![s] = UpdatingState]
    /\ UNCHANGED loadBalanced

\* A server finishes updating
FinishUpdate(s) ==
    /\ version[s] = UpdatingState
    /\ version' = [version EXCEPT ![s] = "new"]
    /\ UNCHANGED loadBalanced

\* Orchestrator returns servers to load balancer
\* Constraint: only fully updated servers can be returned
\* Constraint: must maintain version homogeneity
ReturnToLB(subset) ==
    /\ subset # {}
    /\ subset \subseteq (Servers \ loadBalanced)
    \* All servers in subset must be fully updated (not in updating state)
    /\ \A s \in subset : version[s] = "new"
    \* After adding, the serving set must remain version homogeneous
    /\ LET newLB == loadBalanced \cup subset
           newServing == {s \in newLB : IsServable(s)}
       IN \/ newServing = {}
          \/ \E v \in {"old", "new"} : \A s \in newServing : version[s] = v
    /\ loadBalanced' = loadBalanced \cup subset
    /\ UNCHANGED version

-----------------------------------------------------------------------------

\* Next state relation
Next ==
    \/ \E subset \in (SUBSET Servers \ {{}}) : RemoveFromLB(subset)
    \/ \E s \in Servers : StartUpdate(s)
    \/ \E s \in Servers : FinishUpdate(s)
    \/ \E subset \in (SUBSET Servers \ {{}}) : ReturnToLB(subset)

\* Fairness conditions for progress
\* Fair removal, starting updates, finishing updates, and returning to LB
Fairness ==
    /\ \A s \in Servers : WF_vars(StartUpdate(s))
    /\ \A s \in Servers : WF_vars(FinishUpdate(s))
    /\ \A subset \in (SUBSET Servers \ {{}}) : WF_vars(RemoveFromLB(subset))
    /\ \A subset \in (SUBSET Servers \ {{}}) : WF_vars(ReturnToLB(subset))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

\* SAFETY PROPERTIES

\* Safety: All servers receiving traffic must have homogeneous versions
\* (the load-balanced set must be version-homogeneous among servable servers)
SafetyVersionHomogeneity ==
    VersionHomogeneous

\* Zero downtime: There must always be at least one servable server in the load balancer
ZeroDowntime ==
    \E s \in loadBalanced : IsServable(s)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ SafetyVersionHomogeneity
    /\ ZeroDowntime

-----------------------------------------------------------------------------

\* LIVENESS PROPERTIES

\* All servers eventually reach the new version
AllUpdated ==
    \A s \in Servers : version[s] = "new"

\* All servers eventually updated and back in load balancer
AllUpdatedAndServing ==
    /\ \A s \in Servers : version[s] = "new"
    /\ loadBalanced = Servers

\* Progress: Eventually all servers will be updated
EventualCompletion == <>AllUpdated

\* Stronger liveness: Eventually all servers updated and all back in service
EventualFullService == <>AllUpdatedAndServing

\* A server that is updating will eventually finish
UpdateEventuallyFinishes ==
    \A s \in Servers : (version[s] = UpdatingState) ~> (version[s] = "new")

\* A server removed from LB will eventually be returned (after updating)
RemovedEventuallyReturned ==
    \A s \in Servers : (s \notin loadBalanced) ~> (s \in loadBalanced)

=============================================================================