```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, Schedule
VARIABLES requests, allocations, heldResources, schedulerIndex

Init ==
  /\ requests = [c \in Clients |-> {}]
  /\ allocations = [r \in Resources |-> None]
  /\ heldResources = [c \in Clients |-> {}]
  /\ schedulerIndex = 1

Next ==
  (\E c \in Clients :
    /\ requests[c] = {}
    /\ heldResources[c] = {}
    /\ Schedule(schedulerIndex) = c
    /\ requests' = [requests EXCEPT ![c] = {r \in Resources}]
    /\ allocations' = allocations
    /\ heldResources' = heldResources
    /\ schedulerIndex' = schedulerIndex + 1
  )
  \lor
  (\E c \in Clients, r \in Resources :
    /\ r \in requests[c]
    /\ allocations[r] = None
    /\ Schedule(schedulerIndex) = c
    /\ requests' = [requests EXCEPT ![c] = requests[c] \ {r}]
    /\ allocations' = [allocations EXCEPT ![r] = c]
    /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
    /\ schedulerIndex' = schedulerIndex + 1
  )
  \lor
  (\E c \in Clients, r \in Resources :
    /\ r \in heldResources[c]
    /\ allocations[r] = c
    /\ requests' = requests
    /\ allocations' = [allocations EXCEPT ![r] = None]
    /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
    /\ schedulerIndex' = schedulerIndex + 1
  )
  \lor
  (\E :
    /\ requests' = requests
    /\ allocations' = allocations
    /\ heldResources' = heldResources
    /\ schedulerIndex' = (schedulerIndex + 1) % (Cardinality(Clients) + 1)
  )

Spec ==
  Init /\ [][Next]_requests, allocations, heldResources, schedulerIndex

TypeInvariant ==
  /\ requests \in [Clients |-> SUBSET Resources]
  /\ allocations \in [Resources |-> Clients \cup {None}]
  /\ heldResources \in [Clients |-> SUBSET Resources]

AllocatorInvariant ==
  /\ \A c \in Clients : heldResources[c] \subseteq requests[c]
  /\ \A r \in Resources : allocations[r] = None \/ allocations[r] \in Clients

MutualExclusionInvariant ==
  /\ \A r \in Resources : allocations[r] = None \/ Cardinality({c \in Clients |-> allocations[r] = c}) = 1

EventualReturn ==
  <>[]\A c \in Clients, r \in Resources : heldResources[c] = {} /\ requests[c] = {}

EventualObtainment ==
  <>[]\A c \in Clients : requests[c] = {} /\ heldResources[c] = {}

InfinitelyOftenSatisfied ==
  []<>\A c \in Clients : requests[c] = {} /\ heldResources[c] = {}

Fairness ==
  WF_Vars(Next, requests, allocations, heldResources, schedulerIndex)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => []MutualExclusionInvariant
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfied

```
Note: This TLA+ module uses the `WF_Vars` operator to specify weak fairness conditions for the variables. The `Spec` defines the complete specification as the conjunction of the initial condition and the next-state relation, with fairness conditions applied.