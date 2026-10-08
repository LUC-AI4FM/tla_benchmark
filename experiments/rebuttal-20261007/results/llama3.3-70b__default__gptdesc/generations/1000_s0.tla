```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES clientResources, 
          clientRequests, 
          clientHeldResources

Init == (* Initial conditions *)
        /\ clientResources = [c \in Clients |-> {}]
        /\ clientRequests = [c \in Clients |-> {}]
        /\ clientHeldResources = [c \in Clients |-> {}]

Next == (* Next state relation *)
  \/ \E c \in Clients :
      (* Client issues a request *)
      /\ clientResources[c] = {}
      /\ clientRequests[c] = {}
      /\ clientRequests' = [clientRequests EXCEPT ![c] = Resources]
      /\ clientHeldResources' = clientHeldResources
      /\ clientResources' = clientResources
  \/ \E c \in Clients, r \in Resources :
      (* Client obtains a resource *)
      /\ r \notin clientResources[c]
      /\ r \in clientRequests[c]
      /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \cup {r}]
      /\ clientHeldResources' = [clientHeldResources EXCEPT ![c] = clientHeldResources[c] \cup {r}]
      /\ clientRequests' = clientRequests
  \/ \E c \in Clients, r \in Resources :
      (* Client returns a resource *)
      /\ r \in clientHeldResources[c]
      /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \ {r}]
      /\ clientHeldResources' = [clientHeldResources EXCEPT ![c] = clientHeldResources[c] \ {r}]
      /\ clientRequests' = clientRequests
  \/ (* No change *)
      clientResources' = clientResources
      /\ clientRequests' = clientRequests
      /\ clientHeldResources' = clientHeldResources

Spec == Init /\ [][Next]_<<clientResources, clientRequests, clientHeldResources>>

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]EventualReturn
THEOREM Spec => <>[]EventualObtainment
THEOREM Spec => \A c \in Clients : <>[]NoUnsatisfiedRequests(c)

TypeCorrectness == 
  \A c \in Clients, r \in Resources :
    r \in clientResources[c] => r \in Resources

MutualExclusion == 
  \A r \in Resources :
    \A<<c1, c2>> \in (Clients \X Clients) :
      ~ (r \in clientResources[c1] /\ r \in clientResources[c2])

EventualReturn == 
  \A c \in Clients, r \in Resources :
    <> (r \notin clientHeldResources[c])

EventualObtainment == 
  \A c \in Clients, r \in Resources :
    r \in clientRequests[c] => <> (r \in clientResources[c])

NoUnsatisfiedRequests(c) == 
  clientRequests[c] = {}

Fairness == 
  \A c \in Clients : WF(Next, c)

Symmetry == 
  <<Resources, Clients>>

Counterexample == 
  [ Resources |-> {1, 2}, 
    Clients |-> {c1, c2},
    clientResources |-> [c1 |-> {}, c2 |-> {}],
    clientRequests |-> [c1 |-> {1}, c2 |-> {2}],
    clientHeldResources |-> [c1 |-> {}, c2 |-> {}] ]
```