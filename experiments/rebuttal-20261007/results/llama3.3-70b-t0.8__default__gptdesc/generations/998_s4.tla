```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, ScheduleSeq

VARIABLES clientRequests, clientHolding, scheduleIndex

Init ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolding \in [Clients -> SUBSET Resources]
  /\ scheduleIndex \in Nat

Next ==
  /\ (\/ \* no request
        clientRequests' = clientRequests
      \/ \* issue new request
        (\E c \in Clients :
          /\ clientRequests[c] = {}
          /\ clientHolding[c] = {}
          /\ clientRequests' = [clientRequests EXCEPT ![c] = some subset of Resources]
          /\ clientHolding' = clientHolding
          /\ scheduleIndex' = scheduleIndex
        )
      \/ \* partially satisfy request
        (\E c \in Clients :
          /\ clientRequests[c] # {}
          /\ clientHolding[c] = {}
          /\ clientRequests' = [clientRequests EXCEPT ![c] = some subset of clientRequests[c]]
          /\ clientHolding' = [clientHolding EXCEPT ![c] = some subset of Resources]
          /\ scheduleIndex' = scheduleIndex
        )
      \/ \* return resources early
        (\E c \in Clients :
          /\ clientHolding[c] # {}
          /\ clientRequests' = clientRequests
          /\ clientHolding' = [clientHolding EXCEPT ![c] = some subset of clientHolding[c]]
          /\ scheduleIndex' = scheduleIndex
        )
      \/ \* advance schedule index
        /\ clientRequests' = clientRequests
        /\ clientHolding' = clientHolding
        /\ scheduleIndex' = scheduleIndex + 1
      )
  /\ (scheduleIndex < Length(ScheduleSeq))
  /\ (\A c \in Clients : 
        clientHolding[c] \subseteq Resources
        /\ clientRequests[c] \subseteq Resources)

Spec == Init /\ [][Next]_<<clientRequests, clientHolding, scheduleIndex>>

TypeInvariant ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolding \in [Clients -> SUBSET Resources]
  /\ scheduleIndex \in Nat

MutualExclusionInvariant ==
  /\ (\A c1, c2 \in Clients : 
        c1 # c2 => clientHolding[c1] \cap clientHolding[c2] = {})

AllocatorInvariant ==
  /\ (\A c \in Clients :
        clientRequests[c] # {} => clientHolding[c] \subseteq clientRequests[c])

EventualReturn == 
  <>(\A c \in Clients : clientHolding[c] = {})

EventualObtainment == 
  <>(\A c \in Clients : 
    /\ clientRequests[c] # {}
    /\ clientHolding[c] = clientRequests[c])

InfinitelyOftenSatisfied == 
  []<>(\A c \in Clients :
    /\ clientRequests[c] # {}
    /\ clientHolding[c] = clientRequests[c])

Fairness ==
  /\ WF_<<clientRequests, clientHolding>>(
      (\E c \in Clients : clientHolding[c] # {}))
  /\ SF_<<clientRequests, scheduleIndex>>(\E c \in Clients :
        /\ clientRequests[c] # {}
        /\ clientHolding[c] = {})
  /\ WF_<<scheduleIndex>>(scheduleIndex < Length(ScheduleSeq))

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusionInvariant
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfied
```