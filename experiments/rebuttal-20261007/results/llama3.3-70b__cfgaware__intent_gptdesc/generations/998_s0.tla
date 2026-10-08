---------------------------- MODULE CentralizedResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources
VARIABLES schedule, requests, heldResources, pendingRequests

TypeInvariant == 
  /\ schedule \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ heldResources \in [Clients -> SUBSET Resources]
  /\ pendingRequests \in [Clients -> SUBSET Resources]

Init ==
  /\ schedule = <<
  >>
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [c \in Clients |-> {}]
  /\ pendingRequests = [c \in Clients |-> {}]

Request(c, r) == 
  /\ c \in Clients
  /\ r \subseteq Resources
  /\ pendingRequests[c] = {}
  /\ heldResources[c] = {}
  /\ pendingRequests' = [pendingRequests EXCEPT ![c] = r]
  /\ UNCHANGED <<schedule, requests, heldResources>>

ExtendSchedule(c) == 
  /\ c \in Clients
  /\ pendingRequests[c] /= {}
  /\ schedule' = Append(schedule, c)
  /\ UNCHANGED <<requests, heldResources, pendingRequests>>

Allocate(r, c) == 
  /\ r \in Resources
  /\ c \in Clients
  /\ r \in pendingRequests[c]
  /\ ~ (EXISTS c1 \in Clients : c1 < c & r \in requests[c1])
  /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
  /\ pendingRequests' = [pendingRequests EXCEPT ![c] = pendingRequests[c] \ {r}]
  /\ UNCHANGED <<schedule, requests>>

Return(r, c) == 
  /\ r \in Resources
  /\ c \in Clients
  /\ r \in heldResources[c]
  /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
  /\ pendingRequests' = [pendingRequests EXCEPT ![c] = {}]
  /\ UNCHANGED <<schedule, requests>>

Next ==
  \/ (\E c \in Clients, r \subseteq Resources : Request(c, r))
  \/ (\E c \in Clients : ExtendSchedule(c))
  \/ (\E r \in Resources, c \in Clients : Allocate(r, c))
  \/ (\E r \in Resources, c \in Clients : Return(r, c))

Spec == Init /\ [][Next]_

MutualExclusion == 
  \A c1, c2 \in Clients, r \in Resources : 
    (r \in heldResources[c1]) /\ (r \in heldResources[c2]) => c1 = c2

NoEarlyResource == 
  \A c1, c2 \in Clients, r \in Resources :
    (c1 < c2) /\ (r \in requests[c1]) /\ (r \in heldResources[c2]) => FALSE

ScheduledClients == 
  \A c \in Clients : 
    (c \in schedule) <=> (pendingRequests[c] /= {})

AllocationFeasibility == 
  \A c \in Clients, r \in Resources :
    (c \in schedule) /\ (r \in pendingRequests[c]) => 
      (\E p \in Permutations(schedule) : 
        (\A i \in 1..Len(p) : 
          (\E j \in 1..i-1 : heldResources[p[j]] \cap pendingRequests[p[i]] = {})))

LivenessAssumptions == 
  \A c \in Clients, r \in Resources :
    (r \in heldResources[c]) => <>(r \notin heldResources[c])

AllocatorProgress == 
  \A c \in Clients, r \in Resources :
    (c \in schedule) /\ (r \in pendingRequests[c]) /\ 
      (\A c1 \in Clients : c1 < c => ~ (r \in requests[c1])) =>
      <>(r \in heldResources[c])

SchedulerProgress == 
  \A c \in Clients :
    (pendingRequests[c] /= {}) => <>(c \in schedule)

Theorem == Spec => []MutualExclusion /\ []NoEarlyResource /\ []ScheduledClients
                  /\ []AllocationFeasibility /\ LivenessAssumptions
                  /\ AllocatorProgress /\ SchedulerProgress

=============================================================================