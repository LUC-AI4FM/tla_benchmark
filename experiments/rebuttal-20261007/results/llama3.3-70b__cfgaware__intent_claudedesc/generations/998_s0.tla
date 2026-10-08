---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Clients, Resources
VARIABLES schedule, requests, heldResources

Init ==
  /\ schedule = <<>>
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [r \in Resources |-> None]

Next ==
  \/ \E c \in Clients :
      /\ ~ (requests[c] = {}) 
      /\ heldResources[c] = {}
      /\ schedule' = Append(schedule, c)
      /\ requests' = [requests EXCEPT ![c] = {}]
      /\ heldResources' = heldResources
  \/ \E c \in schedule :
      /\ requests[c] # {}
      /\ \E r \in requests[c] :
          /\ heldResources[r] = None
          /\ heldResources' = [heldResources EXCEPT ![r] = c]
          /\ schedule' = schedule
          /\ requests' = [requests EXCEPT ![c] = requests[c] \ {r}]
  \/ \E c \in Clients :
      /\ requests[c] = {}
      /\ heldResources[c] # {}
      /\ heldResources' = [heldResources EXCEPT ![r \in heldResources[c]] = None]
      /\ schedule' = schedule
      /\ requests' = requests

Spec == Init /\ [][Next]_

THEOREM Spec => [](\A c \in Clients : heldResources[c] \subseteq requests[c])
THEOREM Spec => <>[](\A c \in Clients : requests[c] = {})
THEOREM Spec => [](\A r \in Resources : \A c1, c2 \in Clients : 
  heldResources[r] = c1 /\ heldResources[r] = c2 => c1 = c2)
=============================================================================