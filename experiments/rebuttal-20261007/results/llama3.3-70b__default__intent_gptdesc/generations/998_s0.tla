```tla
MODULE CentralizedResourceAllocator

EXTENDS Integers, FiniteSets

CONSTANTS Resources, Clients
VARIABLES requests, 
          heldResources, 
          schedule, 
          nextClientIndex

Init == 
  /\ requests = [c \in Clients |-> {}]
  /\ heldResources = [r \in Resources |-> None]
  /\ schedule = <<>>
  /\ nextClientIndex = 1

TypeInvariant == 
  /\ requests \in [Clients -> SUBSET Resources]
  /\ heldResources \in [Resources -> Clients \cup {None}]
  /\ schedule \in Seq(Clients)
  /\ nextClientIndex \in Nat

RequestStep(c, newRequests) == 
  /\ c \in Clients
  /\ newRequests \subseteq Resources
  /\ requests' = [requests EXCEPT ![c] = newRequests]
  /\ heldResources' = heldResources
  /\ schedule' = IF schedule = <<>> THEN <<c>> ELSE Append(schedule, c)
  /\ nextClientIndex' = nextClientIndex + 1

AllocationStep(c, allocated) == 
  /\ c \in Clients
  /\ allocated \subseteq (requests[c] \ Resources)
  /\ heldResources' = [heldResources EXCEPT ![r \in allocated |-> c]]
  /\ requests' = [requests EXCEPT ![c] = requests[c] \ allocated]
  /\ schedule' = schedule
  /\ nextClientIndex' = nextClientIndex

ReturnStep(c, returned) == 
  /\ c \in Clients
  /\ returned \subseteq {r \in Resources : heldResources[r] = c}
  /\ heldResources' = [heldResources EXCEPT ![r \in returned |-> None]]
  /\ requests' = requests
  /\ schedule' = IF <<c>> = schedule THEN <<>> ELSE schedule
  /\ nextClientIndex' = nextClientIndex

Next == 
  \/ \E c \in Clients, newRequests \subseteq Resources : 
    RequestStep(c, newRequests)
  \/ \E c \in Clients, allocated \subseteq Resources : 
    AllocationStep(c, allocated)
  \/ \E c \in Clients, returned \subseteq Resources : 
    ReturnStep(c, returned)

MutualExclusion == 
  \A r \in Resources : heldResources[r] = None ∨ heldResources[r] \in Clients

NoEarlyAllocation == 
  \A i \in 1..Len(schedule), \A j \in (i+1)..Len(schedule) :
    \A r \in requests[schedule[j]] : heldResources[r] = None ∨ heldResources[r] = schedule[i]

ScheduledClientsHaveOutstandingRequests == 
  \A c \in schedule : requests[c] # {}

AllocationFeasibility == 
  \A i \in 1..Len(schedule) :
    \A r \in requests[schedule[i]] :
      \E path \in Seq(Clients) : 
        /\ path[1] = schedule[i]
        /\ \A j \in 2..Len(path) : path[j-1] \in schedule /\ path[j] \in Clients
        /\ heldResources[r] = None ∨ heldResources[r] = path[Len(path)]

LivenessAssumptions == 
  \A c \in Clients, \A r \in Resources :
    <<c, r>> \in WF_vars({ReturnStep})

AllocatorMakesProgress == 
  \A c \in Clients, allocated \subseteq Resources :
    <<c, allocated>> \in WF_vars({AllocationStep})

SchedulerSchedulesClients == 
  \A c \in Clients : 
    <<c>> \in WF_vars({RequestStep})

Spec == 
  /\ Init
  /\ [][Next]_requests, heldResources, schedule, nextClientIndex
  /\ TypeInvariant
  /\ MutualExclusion
  /\ NoEarlyAllocation
  /\ ScheduledClientsHaveOutstandingRequests
  /\ AllocationFeasibility
  /\ LivenessAssumptions
  /\ AllocatorMakesProgress
  /\ SchedulerSchedulesClients

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusion
THEOREM Spec => []NoEarlyAllocation
THEOREM Spec => []ScheduledClientsHaveOutstandingRequests
THEOREM Spec => []AllocationFeasibility
```