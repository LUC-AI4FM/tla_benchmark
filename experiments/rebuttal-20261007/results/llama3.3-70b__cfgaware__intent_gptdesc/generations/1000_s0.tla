---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Resources, Clients

VARIABLE clientRequests, clientHolds

ClientRequest == [c \in Clients | -> {}]

TypeInvariant ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolds \in [Clients -> SUBSET Resources]

Exclusivity ==
  /\ TypeInvariant
  /\ \* Resources subseteq UNION {clientHolds[c] : c \in Clients}

RequestStep(c, req) ==
  /\ clientRequests[c] = {}
  /\ clientHolds[c] = {}
  /\ clientRequests' = [clientRequests EXCEPT ![c] = req]
  /\ clientHolds' = clientHolds
  /\ UNCHANGED << >>

GrantStep(c, granted) ==
  /\ clientRequests[c] # {}
  /\ granted \subseteq (clientRequests[c] \cup clientHolds[c])
  /\ granted \subseteq Resources \ {r \in Resources : \E d \in Clients : r \in clientHolds[d]}
  /\ clientRequests' = [clientRequests EXCEPT ![c] = clientRequests[c] \ granted]
  /\ clientHolds' = [clientHolds EXCEPT ![c] = clientHolds[c] \cup granted]
  /\ UNCHANGED << >>

ReturnStep(c, returned) ==
  /\ returned \subseteq clientHolds[c]
  /\ clientRequests' = clientRequests
  /\ clientHolds' = [clientHolds EXCEPT ![c] = clientHolds[c] \ returned]
  /\ UNCHANGED << >>

Next ==
  (\E c \in Clients : \E req \in SUBSET Resources : RequestStep(c, req))
  \/ (\E c \in Clients : \E granted \in SUBSET Resources : GrantStep(c, granted))
  \/ (\E c \in Clients : \E returned \in SUBSET Resources : ReturnStep(c, returned))

Spec ==
  /\ TypeInvariant
  /\ Exclusivity
  /\ [][Next]_<<clientRequests, clientHolds>>

RequestFulfilled(c) == clientRequests[c] = {}

AllocatorLiveness(c) ==
  WF_<<clientRequests, clientHolds>>(\E granted \in SUBSET Resources : GrantStep(c, granted))

ClientReturnLiveness(c) ==
  SF_<<clientRequests, clientHolds>>(clientHolds[c] = {})

RequestSatisfactionLiveness(c) ==
  []<>~ RequestFulfilled(c)

THEOREM Spec => []Exclusivity
THEOREM Spec => \* [][TypeInvariant]
THEOREM Spec => (\A c \in Clients : AllocatorLiveness(c))
THEOREM Spec => (\A c \in Clients : ClientReturnLiveness(c))
THEOREM Spec => (\A c \in Clients : RequestSatisfactionLiveness(c))

=============================================================================