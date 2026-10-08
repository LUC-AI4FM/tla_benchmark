```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES requestQueue, heldResources, pendingRequests

Init == (
  requestQueue = <<>> /\ 
  heldResources = [c \in Clients |-> {}] /\ 
  pendingRequests = [c \in Clients |-> {}]
)

TypeCorrectness == 
  \A c \in Clients : 
    pendingRequests[c] \subseteq Resources /\ 
    heldResources[c] \subseteq Resources

MutualExclusion == 
  \A r \in Resources : 
    \A c1, c2 \in Clients : 
      c1 ≠ c2 => (r \notin heldResources[c1]) \/ (r \notin heldResources[c2])

EventualReturn == 
  \A c \in Clients, r \in Resources : 
    <<c, r>> \in requestQueue => 
    <>(heldResources[c] = {})

EventualObtainment == 
  \A c \in Clients : 
    <<c>> \in requestQueue => 
    <>(pendingRequests[c] = {})

InfinitelyOftenNoUnsatisfiedRequests == 
  \A c \in Clients : 
    <>[] (pendingRequests[c] = {})

Next == 
  (\E c \in Clients, r \in Resources : 
    (<<c>> \notin requestQueue) /\ 
    (heldResources[c] = {}) /\ 
    (pendingRequests[c] = {}) /\ 
    requestQueue' = <<c>> @@ requestQueue /\ 
    heldResources' = [heldResources EXCEPT ![c] = {}] /\ 
    pendingRequests' = [pendingRequests EXCEPT ![c] = {r}]
  ) \/
  (\E c \in Clients, r \in Resources : 
    (<<c, r>> \in requestQueue) /\ 
    (heldResources[c] = {}) /\ 
    (pendingRequests[c] \subseteq Resources) /\ 
    requestQueue' = Tail(requestQueue) /\ 
    heldResources' = [heldResources EXCEPT ![c] = {r}] /\ 
    pendingRequests' = [pendingRequests EXCEPT ![c] = pendingRequests[c] \ {r}]
  ) \/
  (\E c \in Clients, r \in Resources : 
    (<<c>> \notin requestQueue) /\ 
    (heldResources[c] = {r}) /\ 
    requestQueue' = requestQueue /\ 
    heldResources' = [heldResources EXCEPT ![c] = {}] /\ 
    pendingRequests' = [pendingRequests EXCEPT ![c] = {}]
  )

Spec == Init /\ [][Next]_<<requestQueue, heldResources, pendingRequests>>
WF1 == \A c \in Clients : WF_(Next)(c)
SF1 == \A c \in Clients : SF_(Next)(c)

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []MutualExclusion
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenNoUnsatisfiedRequests

SYMMETRY Clients, Resources
```
Note: This TLA+ specification describes the system behavior as described in the problem statement. However, please note that it's recommended to validate this specification against the SANY parser and TLC model checker for correctness.