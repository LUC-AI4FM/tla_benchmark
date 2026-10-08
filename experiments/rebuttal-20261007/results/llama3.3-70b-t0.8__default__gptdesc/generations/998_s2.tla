```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, Schedule

VARIABLES clientRequests,
          clientHeldResources,
          currentScheduleIndex,
          allocatorState,
          resourceAllocations

Init ==
  /\ clientRequests = [c \in Clients |-> {}]
  /\ clientHeldResources = [c \in Clients |-> {}]
  /\ currentScheduleIndex = 1
  /\ allocatorState = [r \in Resources |-> "free"]
  /\ resourceAllocations = [c \in Clients |-> {}]

Next ==
  /\ IF /\ clientRequests' = clientRequests
         /\ clientHeldResources' = clientHeldResources
         /\ currentScheduleIndex' = currentScheduleIndex
         /\ allocatorState' = allocatorState
         /\ resourceAllocations' = resourceAllocations
      THEN TRUE
  \/ \E c \in Clients :
     /\ clientRequests'[c] = clientRequests[c]
     /\ clientHeldResources'[c] = clientHeldResources[c]
     /\ currentScheduleIndex' = currentScheduleIndex
     /\ allocatorState' = [r \in Resources |-> IF r \in clientHeldResources[c]
                                                  THEN "held"
                                                  ELSE allocatorState[r]]
     /\ resourceAllocations'[c] = clientHeldResources[c]
  \/ \E c \in Clients, r \in Resources :
     /\ clientRequests'[c] = clientRequests[c] \cup {r}
     /\ clientHeldResources'[c] = clientHeldResources[c]
     /\ currentScheduleIndex' = currentScheduleIndex
     /\ allocatorState' = [r1 \in Resources |-> IF r1 = r
                                                  THEN "allocated"
                                                  ELSE allocatorState[r1]]
     /\ resourceAllocations'[c] = resourceAllocations[c] \cup {r}
  \/ \E c \in Clients, r \in Resources :
     /\ clientRequests'[c] = clientRequests[c] \ {r}
     /\ clientHeldResources'[c] = clientHeldResources[c] \ {r}
     /\ currentScheduleIndex' = currentScheduleIndex
     /\ allocatorState' = [r1 \in Resources |-> IF r1 = r
                                                  THEN "free"
                                                  ELSE allocatorState[r1]]
     /\ resourceAllocations'[c] = resourceAllocations[c] \ {r}
  \/ \E c \in Clients :
     /\ clientRequests'[c] = {}
     /\ clientHeldResources'[c] = {}
     /\ currentScheduleIndex' = currentScheduleIndex + 1
     /\ allocatorState' = [r \in Resources |-> "free"]
     /\ resourceAllocations'[c] = {}

Spec ==
  /\ Init
  /\ [][Next]_clientRequests, clientHeldResources, currentScheduleIndex, allocatorState, resourceAllocations
  /\ WF_vars(clientRequests, clientHeldResources, currentScheduleIndex, allocatorState, resourceAllocations)
    (\E c \in Clients : clientRequests[c] = {} /\ clientHeldResources[c] = {})
  /\ SF_vars(clientRequests, clientHeldResources, currentScheduleIndex, allocatorState, resourceAllocations)
    (\E r \in Resources : allocatorState[r] = "free")
  /\ SF_vars(clientRequests, clientHeldResources, currentScheduleIndex, allocatorState, resourceAllocations)
    (\E c \in Clients : clientHeldResources[c] = clientRequests[c])
  /\ WF_vars(clientRequests, clientHeldResources, currentScheduleIndex, allocatorState, resourceAllocations)
    (\E c \in Clients, r \in Resources :
       clientRequests[c] = {r} /\ clientHeldResources[c] = {})

THEOREM Spec => [](\A c \in Clients : clientHeldResources[c] \subseteq clientRequests[c])
THEOREM Spec => <>(\A r \in Resources : allocatorState[r] = "free")
THEOREM Spec => <>(\A c \in Clients : clientRequests[c] = {} /\ clientHeldResources[c] = {})
```