```
MODULE ResourceAllocator
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Clients, Resources
VARIABLES schedule, requests, heldResources, pendingRequests

Init ==
  /\ schedule = <<>>
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [r \in Resources |-> None]
  /\ pendingRequests = [c \in Clients |-> {}]

Next ==
  \/ \E c \in Clients :
      /\ pendingRequests[c] /= {}
      /\ schedule' = Append(schedule, c)
      /\ requests' = [requests EXCEPT ![c] = pendingRequests[c]]
      /\ heldResources' = heldResources
      /\ pendingRequests' = [pendingRequests EXCEPT ![c] = {}]
  \/ \E c \in Clients, r \in Resources :
      /\ c \in schedule
      /\ r \in requests[c]
      /\ heldResources[r] = None
      /\ \A d \in schedule : d < c => r \notin requests[d]
      /\ heldResources' = [heldResources EXCEPT ![r] = c]
      /\ IF pendingRequests[c] = {} THEN requests' = [requests EXCEPT ![c] = {}] ELSE requests' = requests
      /\ schedule' = schedule
      /\ pendingRequests' = pendingRequests
  \/ \E c \in Clients, r \in Resources :
      /\ heldResources[r] = c
      /\ requests[c] /= {}
      /\ r \in requests[c]
      /\ heldResources' = [heldResources EXCEPT ![r] = None]
      /\ IF \A x \in Resources : x \notin requests[c] => requests' = [requests EXCEPT ![c] = {}] ELSE requests' = requests
      /\ schedule' = schedule
      /\ pendingRequests' = pendingRequests
  \/ \E c \in Clients :
      /\ pendingRequests[c] /= {}
      /\ schedule' = Append(schedule, Perm(pendingRequests \o DOMAIN))
      /\ requests' = [requests EXCEPT ![c] = pendingRequests[c]]
      /\ heldResources' = heldResources
      /\ pendingRequests' = [pendingRequests EXCEPT ![c] = {}]

Spec ==
  Init /\ [][Next]_schedule

SafetyInv ==
  /\ \A r \in Resources : heldResources[r] = None \/ \E c \in Clients : heldResources[r] = c
  /\ \A c \in schedule : requests[c] /= {}
  /\ \A c \in schedule, r \in Resources :
      /\ r \in requests[c]
      => \E d \in schedule : d <= c /\ r \notin requests[d]

Liveness ==
  /\ []<>[schedule = <<>>]_schedule
  /\ \A c \in Clients, r \in Resources :
      /\ <>[]<>(r \in pendingRequests[c]) => <>[]<>(heldResources[r] = c)
  /\ \A c \in Clients :
      /\ <>[]<>(requests[c] /= {}) => <>[]<>(requests[c] = {})
  /\ \A c \in Clients, r \in Resources :
      /\ heldResources[r] = c => <>[]<>(heldResources[r] = None)

THEOREM Spec => []SafetyInv
THEOREM Spec => Liveness

Fairness ==
  WeakFairness(Next, schedule)
```
Note: The `Perm` operator generates all permutations of a set. The `\o` operator is used for function composition. The `DOMAIN` keyword refers to the domain of a function. The `WeakFairness` predicate ensures that if a client is continuously enabled to make progress, it will eventually do so.