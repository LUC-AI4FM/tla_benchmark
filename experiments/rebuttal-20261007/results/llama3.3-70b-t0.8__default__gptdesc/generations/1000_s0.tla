```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES clientResources, 
          clientRequests, 
          clientHeldResources

Init == (
  clientResources = [c \in Clients |-> {}]
  /\ clientRequests = [c \in Clients |-> {}]
  /\ clientHeldResources = [c \in Clients |-> {}]
)

Next == 
  (\E c \in Clients : 
    (clientResources[c] = {} /\ clientRequests[c] = {}) 
      /\ (clientRequests' = [clientRequests EXCEPT ![c] = Resources])
      /\ UNCHANGED <<clientResources, clientHeldResources>>)
  \/ (\E c \in Clients, r \in Resources :
    (r \in clientRequests[c]) 
      /\ (clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \cup {r}])
      /\ UNCHANGED <<clientRequests, clientHeldResources>>)
  \/ (\E c \in Clients, r \in Resources :
    (r \in clientHeldResources[c]) 
      /\ (clientHeldResources' = [clientHeldResources EXCEPT ![c] = clientHeldResources[c] \ {r}])
      /\ UNCHANGED <<clientResources, clientRequests>>)
  \/ (\E c \in Clients : 
    (clientRequests[c] = {}) 
      /\ (clientResources' = [clientResources EXCEPT ![c] = {}])
      /\ (clientHeldResources' = [clientHeldResources EXCEPT ![c] = {}])
      /\ UNCHANGED clientRequests)

Spec == Init /\ [][Next]_<<clientResources, clientRequests, clientHeldResources>>

TypeCorrectness == \A c \in Clients : clientResources[c] \subseteq Resources
MutualExclusion == \A r \in Resources : 
  \A c1, c2 \in Clients : c1 # c2 => ~(r \in clientResources[c1] /\ r \in clientResources[c2])
EventualReturn == \A c \in Clients : []<>(clientHeldResources[c] = {})
EventualObtainment == \A c \in Clients : 
  <>(\E r \in Resources : r \in clientRequests[c] /\ r \in clientResources[c])
InfinitelyOftenNoUnsatisfiedRequests == \A c \in Clients : <>[]<>(clientRequests[c] = {})

FairnessWeak == WF-vars(Next, <<clientResources, clientRequests, clientHeldResources>>)
FairnessStrong == SF-vars(Next, <<clientResources, clientRequests, clientHeldResources>>)

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []MutualExclusion
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenNoUnsatisfiedRequests

SYMMETRY Resources, Clients

CONSTANT ModelValue
ASSUME 
  ModelValue = [Resources |-> {1, 2}, 
                Clients |-> {a, b}]
```