```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, Schedule
VARIABLES clientRequests, clientHolds, scheduleIndex, allocatedResources

Init ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolds \in [Clients -> SUBSET Resources]
  /\ scheduleIndex \in Nat
  /\ allocatedResources \in [Resources -> Clients \cup {<<None>>}]

Next ==
  /\ IF (\E c \in Clients : 
          clientRequests[c] /= {} /\ clientHolds[c] = {})
      THEN
        /\ \E c \in Clients :
            IF clientRequests[c] /= {} /\ clientHolds[c] = {}
            THEN
              /\ clientHolds' = [clientHolds EXCEPT ![c] = {}]
              /\ allocatedResources' = [allocatedResources EXCEPT ![
                CHOOSE r \in clientRequests[c] : allocatedResources[r] = <<None>>] = c]
              /\ clientRequests' = [clientRequests EXCEPT ![c] = clientRequests[c] \ {CHOOSE r \in clientRequests[c] : allocatedResources[r] = <<None>>}]
            ELSE
              /\ clientHolds' = clientHolds
              /\ allocatedResources' = allocatedResources
              /\ clientRequests' = clientRequests
      ELSE
        /\ clientHolds' = clientHolds
        /\ allocatedResources' = allocatedResources
        /\ clientRequests' = clientRequests
  /\ IF (\E c \in Clients : 
          clientHolds[c] /= {} /\ clientRequests[c] = {})
      THEN
        /\ \E c \in Clients :
            IF clientHolds[c] /= {} /\ clientRequests[c] = {}
            THEN
              /\ clientHolds' = [clientHolds EXCEPT ![c] = {}]
              /\ allocatedResources' = [allocatedResources EXCEPT ![
                CHOOSE r \in clientHolds[c] : TRUE] = <<None>>]
              /\ clientRequests' = clientRequests
            ELSE
              /\ clientHolds' = clientHolds
              /\ allocatedResources' = allocatedResources
              /\ clientRequests' = clientRequests
      ELSE
        /\ clientHolds' = clientHolds
        /\ allocatedResources' = allocatedResources
        /\ clientRequests' = clientRequests
  /\ IF scheduleIndex < Cardinality(Schedule)
  THEN
    /\ scheduleIndex' = scheduleIndex + 1
  ELSE
    /\ scheduleIndex' = 0

Spec ==
  Init /\ [][Next]_clientRequests, clientHolds, scheduleIndex, allocatedResources

TypeInvariant ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolds \in [Clients -> SUBSET Resources]
  /\ scheduleIndex \in Nat
  /\ allocatedResources \in [Resources -> Clients \cup {<<None>>}]

MutualExclusionInvariant ==
  /\ \A r \in Resources : 
      <<allocatedResources[r] = <<None>>> \lor (\E c \in Clients : allocatedResources[r] = c)

AllocatorInvariant1 ==
  /\ \A c \in Clients :
      clientHolds[c] \subseteq clientRequests[c]

AllocatorInvariant2 ==
  /\ \A r \in Resources :
      allocatedResources[r] /= <<None>> => allocatedResources[r] \in Clients

EventualReturn ==
  <>[](\A c \in Clients : 
        clientHolds[c] = {})

EventualObtainment ==
  <>[](\A c \in Clients : 
        clientRequests[c] = {})

InfinitelyOftenSatisfied ==
  []<>(\E c \in Clients :
        clientRequests[c] /= {} /\ clientHolds[c] = clientRequests[c])

Theorem == Spec => []TypeInvariant /\ []MutualExclusionInvariant
                  /\ []AllocatorInvariant1 /\ []AllocatorInvariant2
                  /\ EventualReturn /\ EventualObtainment /\ InfinitelyOftenSatisfied

Fairness ==
  /\ WF_vars(Next, clientHolds)
  /\ SF_vars(Next, allocatedResources)

THEOREM Theorem
```