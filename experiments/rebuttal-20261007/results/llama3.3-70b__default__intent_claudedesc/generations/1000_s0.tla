```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources
VARIABLES requests, heldResources, availableResources

Init ==
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [c \in Clients |-> {}]
  /\ availableResources = Resources

Next ==
  \/ \E c \in Clients :
      /\ requests[c] = {}
      /\ heldResources[c] = {}
      /\ requests' = [requests EXCEPT ![c] = some subset \in SUBSET Resources]
      /\ heldResources' = heldResources
      /\ availableResources' = availableResources
  \/ \E c \in Clients, r \in SUBSET Resources :
      /\ requests[c] /= {}
      /\ r /= {}
      /\ r \subseteq (availableResources \cap requests[c])
      /\ heldResources' = [heldResources EXCEPT ![c] = @ \cup r]
      /\ availableResources' = availableResources \ r
      /\ requests' = requests
  \/ \E c \in Clients, r \in SUBSET Resources :
      /\ requests[c] = {}
      /\ r /= {}
      /\ r \subseteq heldResources[c]
      /\ heldResources' = [heldResources EXCEPT ![c] = @ \ r]
      /\ availableResources' = availableResources \cup r
      /\ requests' = requests

Spec ==
  Init /\ [][Next]_<<requests, heldResources, availableResources>>
  /\ WF_<<requests, heldResources, availableResources>>(\E c \in Clients : 
      <>(\A r \in SUBSET Resources : 
          (requests[c] /= {} /\ r \subseteq requests[c]) 
          ==> <>(heldResources[c] = r))))
  /\ SF_<<requests, heldResources, availableResources>>(\A c \in Clients :
      []<>(requests[c] = {} /\ heldResources[c] = {}))

THEOREM Spec => []MutualExclusion
 MutualExclusion == \A r \in Resources : 
   \A c1, c2 \in Clients : 
     heldResources[c1] \cap heldResources[c2] = {} 

THEOREM Spec => EventualReturn
EventualReturn == \A c \in Clients :
  []<>(requests[c] = {} ==> <>(heldResources[c] = {}))

THEOREM Spec => EventualAllocation
EventualAllocation == \A c \in Clients, r \in Resources :
  []<><>((r \in requests[c]) /\ (r \in heldResources[c]))

THEOREM Spec => InfiniteSatisfiability
InfiniteSatisfiability == \A c \in Clients :
  []<>[]<>(requests[c] = {} /\ heldResources[c] = requests[c])
```