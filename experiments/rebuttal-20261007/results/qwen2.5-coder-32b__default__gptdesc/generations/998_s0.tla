------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Clients, Resources, Schedule

VARIABLES held, requested, satisfied, scheduleIndex

Init == 
  /\ held = [c \in Clients |-> {}]
  /\ requested = [c \in Clients |-> {}]
  /\ satisfied = [c \in Clients |-> FALSE]
  /\ scheduleIndex = 1

Next ==
  \/ \E c \in Clients : 
      /\ requested[c] = {}
      /\ held[c] = {}
      /\ \E r \in Resources : requested' = [requested EXCEPT ![c] = {r}]
      /\ UNCHANGED <<held, satisfied, scheduleIndex>>
  \/ \E c \in Clients :
      /\ satisfied[c]
      /\ held'[c] = {}
      /\ satisfied' = [satisfied EXCEPT ![c] = FALSE]
      /\ UNCHANGED <<requested, scheduleIndex>>
  \/ \E c \in Clients, r \in requested[c] :
      /\ r \notin held[c]
      /\ r \notin UNION {held[c'] : c' \in Clients}
      /\ held'[c] = held[c] \cup {r}
      /\ UNCHANGED <<requested, satisfied, scheduleIndex>>
  \/ \E i \leq Len(Schedule) :
      /\ scheduleIndex = i
      /\ scheduleIndex' = (i + 1) % (Len(Schedule) + 1)
      /\ UNCHANGED <<held, requested, satisfied>>

Spec ==
  Init /\ [][Next]_<<held, requested, satisfied, scheduleIndex>> 

TypeOK ==
  /\ held \in [Clients -> SUBSET Resources]
  /\ requested \in [Clients -> SUBSET Resources]
  /\ satisfied \in [Clients -> BOOLEAN]
  /\ scheduleIndex \in 1..Len(Schedule)

MutualExclusion ==
  \A r \in Resources : Cardinality({c \in Clients : r \in held[c]}) <= 1

AllocatorInvariant ==
  \A c \in Clients :
    /\ (requested[c] = {}) => (satisfied[c] = FALSE)
    /\ (held[c] = {}) => (satisfied[c] = FALSE)

EventualReturn ==
  WF_<<held, requested, satisfied, scheduleIndex>>[Next]
  /\ \A c \in Clients : 
      <>(\E r \in Resources : r \in held[c]) => <>(held'[c] = {})

EventualObtainment ==
  WF_<<held, requested, satisfied, scheduleIndex>>[Next]
  /\ \A c \in Clients :
      <>(requested[c] /= {}) => <>(\E r \in Resources : r \in held[c])

InfinitelyOftenSatisfied ==
  SF_<<held, requested, satisfied, scheduleIndex>>[Next]
  /\ \A c \in Clients :
     <>[](\E r \in Resources : r \in held[c]) => <>[](satisfied'[c] = TRUE)

Fairness ==
  WF_<<held, requested, satisfied, scheduleIndex>>[Next]
  /\ SF_<<held, requested, satisfied, scheduleIndex>>[Next]

=============================================================================