```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, Schedule
VARIABLES clientRequests, allocatedResources, scheduleIndex

Init ==
  /\ clientRequests \in [Clients |-> {}]
  /\ allocatedResources \in [Clients |-> {}]
  /\ scheduleIndex = 1

Next ==
  \/ \E c \in Clients :
      /\ clientRequests[c] = {}
      /\ allocatedResources[c] = {}
      /\ clientRequests' = [clientRequests EXCEPT ![c] = {r \in Resources : r \notin allocatedResources[c]}]
      /\ allocatedResources' = allocatedResources
      /\ scheduleIndex' = scheduleIndex
  \/ \E c \in Clients :
      /\ clientRequests[c] /= {}
      /\ allocatedResources' = [allocatedResources EXCEPT ![c] = allocatedResources[c] \cup {r \in Resources : r \in clientRequests[c]}]
      /\ clientRequests' = [clientRequests EXCEPT ![c] = {}]
      /\ scheduleIndex' = Schedule(scheduleIndex)
  \/ \E c \in Clients :
      /\ allocatedResources[c] /= {}
      /\ clientRequests' = clientRequests
      /\ allocatedResources' = [allocatedResources EXCEPT ![c] = {}]
      /\ scheduleIndex' = scheduleIndex

Spec ==
  Init /\ [][Next]_clientRequests, allocatedResources, scheduleIndex

TypeInvariant ==
  /\ clientRequests \in [Clients |-> SUBSET Resources]
  /\ allocatedResources \in [Clients |-> SUBSET Resources]

AllocatorInvariant ==
  /\ \A c1, c2 \in Clients : c1 /= c2 => allocatedResources[c1] \cap allocatedResources[c2] = {}
  /\ \A c \in Clients : clientRequests[c] \cap allocatedResources[c] = {}

EventualReturn ==
  <>[]\A c \in Clients : allocatedResources[c] = {} <=> clientRequests[c] = {}

EventualObtainment ==
  []<> \A c \in Clients, r \in Resources :
    clientRequests[c] /= {} /\ r \in clientRequests[c]
      => <>(r \in allocatedResources[c])

InfinitelyOftenSatisfied ==
  []<>\A c \in Clients : clientRequests[c] = {}

Fairness ==
  /\ WF_vars(Next, clientRequests, allocatedResources, scheduleIndex)
  /\ SF_vars(Next, clientRequests, allocatedResources, scheduleIndex)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfied
```