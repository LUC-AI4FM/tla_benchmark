---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources
VARIABLES requests, heldResources, availableResources

Init ==
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [r \in Resources |-> None]
  /\ availableResources = Resources

TypeInvariant ==
  /\ requests \in [Clients -> SUBSET Resources]
  /\ heldResources \in [Resources -> Clients \cup {None}]
  /\ availableResources \subseteq Resources

Request(c, req) ==
  /\ c \in Clients
  /\ req \subseteq Resources
  /\ req /= {}
  /\ requests[c] = {}
  /\ heldResources[resources] = None << resources \in Resources >>
  /\ requests' = [requests EXCEPT ![c] = req]
  /\ heldResources' = heldResources
  /\ availableResources' = availableResources

Allocate(c, alloc) ==
  /\ c \in Clients
  /\ alloc \subseteq Resources
  /\ alloc /= {}
  /\ alloc \subseteq availableResources
  /\ requests[c] /= {}
  /\ heldResources' = [heldResources EXCEPT ![r \in alloc |-> c]]
  /\ availableResources' = availableResources \ alloc
  /\ requests' = requests

Return(c, ret) ==
  /\ c \in Clients
  /\ ret \subseteq Resources
  /\ ret /= {}
  /\ heldResources[ret] = c << resources \in ret >>
  /\ heldResources' = [heldResources EXCEPT ![r \in ret |-> None]]
  /\ availableResources' = availableResources \cup ret
  /\ requests' = requests

Next ==
  \/ \E c \in Clients, req \in SUBSET Resources : Request(c, req)
  \/ \E c \in Clients, alloc \in SUBSET Resources : Allocate(c, alloc)
  \/ \E c \in Clients, ret \in SUBSET Resources : Return(c, ret)

Spec ==
  Init /\ [][Next]_<<requests, heldResources, availableResources>>

THEOREM Spec => []MutualExclusion
THEOREM Spec => []EventualReturn
THEOREM Spec => []EventualAllocation
THEOREM Spec => []InfiniteSatisfiability

MutualExclusion ==
  \A r \in Resources : heldResources[r] = None \/ heldResources[r] \in Clients

EventualReturn ==
  \A c \in Clients : requests[c] = {} => <><heldResources[resources] = None << resources \in Resources >>

EventualAllocation ==
  \A c \in Clients, r \in Resources : requests[c] /= {} /\ r \in requests[c] => <><heldResources[r] = c>

InfiniteSatisfiability ==
  \A c \in Clients : []<>requests[c] = {}

Fairness ==
  SF_VARIABLES <<requests, heldResources, availableResources>>
  /\ WF_VARIABLES <<requests, heldResources, availableResources>>

=============================================================================