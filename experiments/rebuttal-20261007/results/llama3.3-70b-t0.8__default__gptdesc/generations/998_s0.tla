```
MODULE ResourceAllocator
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources, Schedule

VARIABLES clientRequests, clientHolds, allocatorState, scheduleIndex

Init ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolds \in [Clients -> SUBSET Resources]
  /\ allocatorState \in [Resources -> UNION {<< >>, Clients}]
  /\ scheduleIndex \in Nat

Next ==
  \/ \E c \in Clients :
    /\ clientRequests[c] /= {}
    /\ clientHolds[c] = {}
    /\ allocatorState' = [allocatorState EXCEPT ![r \in Resources] = IF r \in clientRequests[c] THEN {c} ELSE @)
    /\ clientRequests' = [clientRequests EXCEPT ![c] = {}]
    /\ clientHolds' = [clientHolds EXCEPT ![c] = {}]
    /\ scheduleIndex' = scheduleIndex
  \/ \E c \in Clients :
    /\ clientHolds[c] /= {}
    /\ allocatorState' = [allocatorState EXCEPT ![r \in Resources] = IF r \in clientHolds[c] THEN << >> ELSE @)
    /\ clientRequests' = [clientRequests EXCEPT ![c] = {}]
    /\ clientHolds' = [clientHolds EXCEPT ![c] = {}]
    /\ scheduleIndex' = scheduleIndex
  \/ \E c \in Clients :
    /\ clientRequests[c] /= {}
    /\ allocatorState' = [allocatorState EXCEPT ![r \in Resources] = IF r \in clientRequests[c] THEN {c} ELSE @)
    /\ clientRequests' = [clientRequests EXCEPT ![c] = {}]
    /\ clientHolds' = [clientHolds EXCEPT ![c] = clientHolds[c] \cup {r \in Resources : allocatorState'[r] = {c}}]
    /\ scheduleIndex' = scheduleIndex + 1
  \/ scheduleIndex < Len(Schedule)
    /\ scheduleIndex' = scheduleIndex + 1
    /\ clientRequests' = clientRequests
    /\ clientHolds' = clientHolds
    /\ allocatorState' = allocatorState

Spec ==
  Init /\ [][Next]_<<clientRequests, clientHolds, allocatorState, scheduleIndex>>

TypeInvariant ==
  /\ clientRequests \in [Clients -> SUBSET Resources]
  /\ clientHolds \in [Clients -> SUBSET Resources]
  /\ allocatorState \in [Resources -> UNION {<< >>, Clients}]
  /\ scheduleIndex \in Nat

MutualExclusionInvariant ==
  /\ \A r \in Resources : allocatorState[r] \subseteq Clients
  /\ \A c \in Clients : clientHolds[c] \subseteq Resources

AllocatorInvariant1 ==
  /\ \A c \in Clients : clientRequests[c] = {} \/ clientHolds[c] = {}

AllocatorInvariant2 ==
  /\ \A r \in Resources : allocatorState[r] = << >> \/ allocatorState[r] \subseteq {c \in Clients : r \in clientRequests[c]}

EventualReturn ==
  <>[]\A c \in Clients : clientHolds[c] /= {} ~> clientHolds[c] = {}

EventualObtainment ==
  <>[]\A c \in Clients, r \in Resources : r \in clientRequests[c] ~> r \in clientHolds[c]

InfinitelyOftenSatisfied ==
  []<>\A c \in Clients : clientRequests[c] /= {} /\ clientHolds[c] = {}

Fairness1 ==
  WF_Vars(Next, <<clientRequests, clientHolds>>)

Fairness2 ==
  SF_Vars(Next, <<allocatorState, scheduleIndex>>)
```