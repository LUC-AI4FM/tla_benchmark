---------------------------- MODULE ResourceAllocator ----------------------------

EXTENDS TLC, FiniteSets, Sequences

CONSTANTS Clients, Resources, Schedule

VARIABLES Requests, Allocations, HeldResources, SatisfiedRequests

Init == /\ Requests = [c \in Clients |-> {}]
        /\ Allocations = [r \in Resources |-> <<>>]
        /\ HeldResources = [c \in Clients |-> {}]
        /\ SatisfiedRequests = {}

Next ==
  \/ \E c \in Clients, r \in Resources :
      Requests'[c] = (IF r \notin Requests[c] THEN Requests[c] \cup {r} ELSE Requests[c])
      /\ Allocations' = Allocations
      /\ HeldResources' = HeldResources
      /\ SatisfiedRequests' = SatisfiedRequests
  \/ \E c \in Clients, r \in Resources :
      Requests'[c] = (IF r \notin Requests[c] THEN Requests[c] \cup {r} ELSE Requests[c])
      /\ Allocations'[r] = Append(Allocations[r], <<c>>)
      /\ HeldResources' = [HeldResources EXCEPT ![c] = HeldResources[c] \cup {r}]
      /\ SatisfiedRequests' = (IF #(HeldResources[c] \cup {r}) >= #(Schedule) THEN SatisfiedRequests \cup {c} ELSE SatisfiedRequests)
  \/ \E c \in Clients, r \in Resources :
      Requests'[c] = (IF HeldResources[c] /= {} THEN {} ELSE Requests[c])
      /\ Allocations'[r] = Head(Allocations[r]) # c => Allocations[r]
                           [] [Allocations EXCEPT ![r] = Tail(Allocations[r])]
      /\ HeldResources' = [HeldResources EXCEPT ![c] = HeldResources[c] \ {r}]
      /\ SatisfiedRequests' = (IF HeldResources'[c] = {} THEN SatisfiedRequests \ {c} ELSE SatisfiedRequests)

Spec ==
  /\ Init
  /\ [][Next]_<<Requests, Allocations, HeldResources, SatisfiedRequests>>
  /\ WF_<<c \in Clients : Requests[c] /= {}>>_<<Requests, Allocations, HeldResources, SatisfiedRequests>>
  /\ SF_<<r \in Resources : Allocations[r] /= <<>>>_<<Requests, Allocations, HeldResources, SatisfiedRequests>>
  /\ SF_<<Schedule' = Schedule>>_<<Requests, Allocations, HeldResources, SatisfiedRequests>>

TypeOK ==
  /\ Requests \in [Clients -> SUBSET Resources]
  /\ Allocations \in [Resources -> SEQ Clients]
  /\ HeldResources \in [Clients -> SUBSET Resources]
  /\ SatisfiedRequests \in SUBSET Clients

MutualExclusion == 
  \A r \in Resources, c1, c2 \in Clients :
    c1 /= c2 => r \notin HeldResources[c1] \/ r \notin HeldResources[c2]

AllocatorInvariant ==
  \A r \in Resources :
    Len(Allocations[r]) = Cardinality({c \in Clients : r \in HeldResources[c]})

EventualReturn ==
  \A c \in Clients, r \in Resources :
    <>(r \notin HeldResources[c])

EventualObtainment ==
  \A c \in Clients, r \in Resources :
    <>(r \in HeldResources[c])

InfinitelyOftenSatisfiedRequests ==
  []<>(SatisfiedRequests /= {})

THEOREM Spec => []TypeOK
THEOREM Spec => [](MutualExclusion)
THEOREM Spec => [](AllocatorInvariant)
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfiedRequests

=============================================================================