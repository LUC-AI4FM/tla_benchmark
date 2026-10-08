```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES clientResources, 
          clientRequests, 
          clientReturns,
          requestQueue

Init == (* Initial state *)
        /\ clientResources = [c \in Clients |-> {}]
        /\ clientRequests = [c \in Clients |-> {}]
        /\ clientReturns = [c \in Clients |-> {}]
        /\ requestQueue = <<>>

Next == (* Next state *)
         \/ \E c \in Clients :
               (* Client issues a new request *)
               (clientResources[c] = {} /\ clientRequests[c] = {}
                /\ clientReturns[c] = {}
                /\ requestQueue' = Append(requestQueue, c)
                /\ UNCHANGED <<clientResources, clientRequests, clientReturns>>)
         \/ \E r \in Resources :
               (* Allocate a resource to the first client in the queue *)
               (requestQueue # <> 
                /\ clientResources'[Head(requestQueue)] = clientResources[Head(requestQueue)] \cup {r}
                /\ clientRequests'[Head(requestQueue)] = clientRequests[Head(requestQueue)] \ {r}
                /\ requestQueue' = Tail(requestQueue)
                /\ UNCHANGED <<clientReturns>>)
         \/ \E c \in Clients, r \in Resources :
               (* Client returns a held resource *)
               (r \in clientResources[c]
                /\ clientResources' = [clientResources EXCEPT ![c] = clientResources[c] \ {r}]
                /\ clientReturns'[c] = clientReturns[c] \cup {r}
                /\ UNCHANGED <<requestQueue, clientRequests>>)
         \/ (* Queue is unchanged *)
             requestQueue' = requestQueue
             /\ UNCHANGED <<clientResources, clientRequests, clientReturns>>

Spec == Init /\ [][Next]_

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]EventualReturn_c
THEOREM Spec => <>[]EventualObtainment_c
THEOREM Spec => \A c \in Clients : WF_(c, Next)
THEOREM Spec => \A c \in Clients : SF_(c, Next)

TypeCorrectness == 
  \A c \in Clients : clientResources[c] \subseteq Resources
  /\ \A c \in Clients : clientRequests[c] \subseteq Resources

MutualExclusion == 
  \A r \in Resources : \A c1, c2 \in Clients : 
    (r \in clientResources[c1]) => (r \notin clientResources[c2])

EventualReturn_c == 
  \A c \in Clients, r \in Resources :
    (r \in clientReturns[c]) => <>~(r \in clientResources[c])

EventualObtainment_c == 
  \A c \in Clients : 
    <>[]~(clientRequests[c] = {})

WF_(c, Next) == 
  \A s \in [Next]_ : <<s>> \in Fairness_(c)

SF_(c, Next) == 
  \A s \in [Next]_ : (s \in Enabled(<>[]~(clientRequests[c] = {}))) => <>~(clientRequests[c] = {})

Fairness_(c) == 
  {<<s>> \in Seq(Next) : <<s>>[1] = c}

SymmetryExpression ==
  \E perm \in Permutations(Clients) :
    [][\A c \in Clients : clientResources'[perm[c]] = clientResources[c]]

CounterexampleValueStructure ==
  [ Resources |-> {r1, r2}, 
    Clients |-> {c1, c2},
    clientResources |-> [c1 |-> {}, c2 |-> {}],
    clientRequests |-> [c1 |-> {r1}, c2 |-> {r2}],
    requestQueue |-> <<c1>> ]
```