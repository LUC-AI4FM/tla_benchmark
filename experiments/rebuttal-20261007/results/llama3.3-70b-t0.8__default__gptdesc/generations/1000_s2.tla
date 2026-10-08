```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES clientResources, clientRequests, clientHeld

Init ==
  /\ clientResources \in [Clients -> SUBSET Resources]
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHeld \in [Clients -> SUBSET Resources]
  /\ clientResources = [c \in Clients |-> {}]
  /\ clientRequests = [c \in Clients |-> {}]
  /\ clientHeld = [c \in Clients |-> {}]

Next ==
  \/ \E c \in Clients :
    /\ clientResources[c] = {}
    /\ clientRequests[c] = {}
    /\ clientRequests' = [clientRequests EXCEPT ![c] = some subset \subseteq Resources]
    /\ clientResources' = clientResources
    /\ clientHeld' = clientHeld
  \/ \E c \in Clients, r \in Resources :
    /\ r \in clientRequests[c]
    /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \cup {r}]
    /\ clientRequests' = [clientRequests EXCEPT ![c] = clientRequests[c] \setminus {r}]
    /\ clientHeld' = [clientHeld EXCEPT ![c] = clientHeld[c] \cup {r}]
  \/ \E c \in Clients, r \in Resources :
    /\ r \in clientHeld[c]
    /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \setminus {r}]
    /\ clientRequests' = clientRequests
    /\ clientHeld' = [clientHeld EXCEPT ![c] = clientHeld[c] \setminus {r}]

Spec == Init /\ [][Next]_<<clientResources, clientRequests, clientHeld>>

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]EventualReturn
THEOREM Spec => <>[]EventualObtainment
THEOREM Spec => \A c \in Clients : <<clientResources[c], clientRequests[c], clientHeld[c]]>_temporal

TypeCorrectness == \A c \in Clients : clientResources[c] \subseteq Resources
MutualExclusion == \A r \in Resources : \A<<c1, c2>> \in (Clients \X Clients) : 
  ~(r \in clientResources[c1] /\ r \in clientResources[c2])
EventualReturn == \A c \in Clients : <>(clientHeld[c] = {})
EventualObtainment == \A c \in Clients, r \in Resources : 
  <>((r \in clientRequests[c]) => (r \in clientResources[c]))
Symmetry == \A<<c1, c2>> \in (Clients \X Clients) :
  PERMUTE <<clientResources[c1], clientRequests[c1], clientHeld[c1]>>,
             <<clientResources[c2], clientRequests[c2], clientHeld[c2]>>
Counterexample == 
  /\ Resources = {r1, r2}
  /\ Clients = {c1, c2}
  /\ clientResources = [c1 |-> {}, c2 |-> {}]
  /\ clientRequests = [c1 |-> {r1}, c2 |-> {r2}]
  /\ clientHeld = [c1 |-> {}, c2 |-> {}]

FAIRNESS <<clientResources, clientRequests, clientHeld>>_weak
```
Note: This specification is written based on the given description. It may require adjustments and refinements to accurately model the system's behavior.