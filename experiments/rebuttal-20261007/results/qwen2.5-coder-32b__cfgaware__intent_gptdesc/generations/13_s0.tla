------------------------------- MODULE RollingUpdate -------------------------------

CONSTANTS 
    \* The set of servers in the cluster
    Servers,
    
    \* A distinguished representation for an "updating" intermediate state
    UPDATING

VARIABLES 
    \* The current version of each server
    versions,
    
    \* The set of servers currently serving traffic (in the load-balanced set)
    activeServers
    
ASSUME 
    \* Servers is a non-empty finite set
    /\ Servers \in Fin(UNIV) 
    /\ Servers /= {}
    
    \* UPDATING is not in the initial versions of any server
    /\ \A s \in Servers: versions[s] # UPDATING

CONSTANTS 
    \* The initial version of all servers
    INITIAL_VERSION,
    
    \* The target version to update to
    TARGET_VERSION
    
VARIABLES 
    \* The set of servers currently being updated by the orchestrator
    updatingServers

ASSUME 
    \* INITIAL_VERSION and TARGET_VERSION are distinct and not equal to UPDATING
    /\ INITIAL_VERSION # TARGET_VERSION
    /\ INITIAL_VERSION # UPDATING
    /\ TARGET_VERSION # UPDATING
    
    \* Initially, all servers have the same version and are active
    /\ versions = [s \in Servers |-> INITIAL_VERSION]
    /\ activeServers = Servers

\* Next-state relation for a server starting an update
StartUpdate ==
    \E s \in activeServers:
        \/ /\ updatingServers' = updatingServers \cup {s}
           /\ versions' = [versions EXCEPT ![s] = UPDATING]
           /\ UNCHANGED activeServers
           
\* Next-state relation for a server completing an update
FinishUpdate ==
    \E s \in updatingServers:
        \/ /\ updatingServers' = updatingServers \ {s}
           /\ versions' = [versions EXCEPT ![s] = TARGET_VERSION]
           /\ UNCHANGED activeServers

\* Next-state relation for the orchestrator removing servers from load balancer
RemoveFromLoadBalancer ==
    \E S \subseteq activeServers:
        \/ /\ updatingServers' = updatingServers \cup S
           /\ activeServers' = activeServers \ S
           /\ UNCHANGED versions

\* Next-state relation for the orchestrator returning servers to load balancer
ReturnToLoadBalancer ==
    \E S \subseteq updatingServers:
        \/ /\ updatingServers' = updatingServers \ S
           /\ activeServers' = activeServers \cup S
           /\ UNCHANGED versions

Spec == 
    VARIABLES versions, activeServers, updatingServers
    INIT
        /\ versions = [s \in Servers |-> INITIAL_VERSION]
        /\ activeServers = Servers
        /\ updatingServers = {}
    NEXT
        \/ StartUpdate
        \/ FinishUpdate
        \/ RemoveFromLoadBalancer
        \/ ReturnToLoadBalancer

\* Safety: At any instant, every server that is receiving traffic must be in a compatible version state with all other servers receiving traffic.
VersionHomogeneity ==
    \A s1, s2 \in activeServers: versions[s1] = versions[s2]

\* Zero downtime: There must always be at least one server in the load-balanced set that is able to serve requests (the load-balanced set must never be empty or composed only of servers in an intermediate non-serving state).
ZeroDowntime ==
    /\ activeServers /= {}
    /\ \E s \in activeServers: versions[s] # UPDATING

\* Progress/termination: The orchestrated update procedure should be fair and eventually complete: if an update is initiated it will eventually finish and all servers will reach the updated state.
Termination ==
    \A s \in Servers: versions[s] = TARGET_VERSION

\* Liveness under concurrency: Concurrent server update activities and the orchestrator’s actions should be allowed, but the orchestrator must wait for removed servers to finish updating before returning them to the load balancer.
Liveness ==
    WF_vars_(Spec, <<activeServers, updatingServers>>)

THEOREM Spec => []VersionHomogeneity
THEOREM Spec => []ZeroDowntime
THEOREM Spec => <>([]Termination)
THEOREM Spec => Liveness

=============================================================================