```tla
MODULE ResourceAllocator

EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources

VARIABLES clientRequests,
          clientHolds,
          freeResources

Init ==
  /\ clientRequests = [c \in Clients |-> {}]
  /\ clientHolds = [c \in Clients |-> {}]
  /\ freeResources = Resources

Next ==
  \/ \E c \in Clients :
      /\ clientRequests[c] = {}
      /\ clientHolds[c] = {}
      /\ clientRequests' = [clientRequests EXCEPT ![c] = {r \in Resources : r \in Resources}]
      /\ clientHolds' = clientHolds
      /\ freeResources' = freeResources
  \/ \E c \in Clients, subset \subseteq Resources :
      /\ subset /= {}
      /\ subset \subseteq clientRequests[c]
      /\ subset \subseteq freeResources
      /\ clientRequests' = [clientRequests EXCEPT ![c] = clientRequests[c] \ subset]
      /\ clientHolds' = [clientHolds EXCEPT ![c] = clientHolds[c] \cup subset]
      /\ freeResources' = freeResources \ subset
  \/ \E c \in Clients, subset \subseteq Resources :
      /\ subset /= {}
      /\ subset \subseteq clientHolds[c]
      /\ clientRequests' = clientRequests
      /\ clientHolds' = [clientHolds EXCEPT ![c] = clientHolds[c] \ subset]
      /\ freeResources' = freeResources \cup subset

Spec ==
  /\ Init
  /\ [][Next]_<<clientRequests, clientHolds, freeResources>>
  /\ WF_<<clientRequests, clientHolds, freeResources>>(Next)
  /\ \A c \in Clients : 
      <>[]<>(clientRequests[c] = {})

THEOREM Spec => []\A r \in Resources : 
  \A c1, c2 \in Clients : 
    ~(r \in clientHolds[c1] /\ r \in clientHolds[c2])

THEOREM Spec => []\A c \in Clients : 
  clientRequests[c] \subseteq Resources
  /\ clientHolds[c] \subseteq Resources

THEOREM Spec => <>[]<>(\A c \in Clients : clientRequests[c] = {})

THEOREM Spec => \A c \in Clients : 
  []<>clientRequests[c] = {}

THEOREM Spec => \A c \in Clients : 
  <>[]<>(clientHolds[c] = {})
```