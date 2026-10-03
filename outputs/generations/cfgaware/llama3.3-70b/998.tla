---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources
VARIABLES requests, allocations, schedule, nextClient

TypeOK == 
  /\ requests \in [Clients -> SUBSET Resources]
  /\ allocations \in [Resources -> Clients \cup {<<"none">>}]
  /\ schedule \in Seq(Clients)
  /\ nextClient \in 1..Len(schedule)

RequestEnabled(client) == 
  /\ client \in Clients
  /\ requests[client] /= {}
  /\ client = schedule[nextClient]

Allocate(client, resource) == 
  /\ RequestEnabled(client)
  /\ resource \in requests[client]
  /\ allocations[resource] = <<"none">>
  /\ allocations' = [allocations EXCEPT ![resource] = client]
  /\ nextClient' = IF nextClient < Len(schedule) THEN nextClient + 1 ELSE 1
  /\ UNCHANGED <<requests, schedule>>

Return(client, resource) == 
  /\ client \in Clients
  /\ resource \in requests[client]
  /\ allocations[resource] = client
  /\ allocations' = [allocations EXCEPT ![resource] = <<"none">>]
  /\ nextClient' = IF nextClient < Len(schedule) THEN nextClient + 1 ELSE 1
  /\ UNCHANGED <<requests, schedule>>

Request(client) == 
  /\ client \in Clients
  /\ requests[client] /= {}
  /\ RequestEnabled(client)
  /\ allocations' = allocations
  /\ requests' = [requests EXCEPT ![client] = {}]
  /\ nextClient' = IF nextClient < Len(schedule) THEN nextClient + 1 ELSE 1
  /\ UNCHANGED schedule

Next == 
  \E client \in Clients : 
    \E resource \in Resources : 
      (Allocate(client, resource)) 
      \/ (Return(client, resource))
  \/ (\E client \in Clients : Request(client))

Spec == 
  /\ TypeOK
  /\ requests = [c \in Clients |-> {}]
  /\ allocations = [r \in Resources |-> <<"none">>]
  /\ schedule = <<>>
  /\ nextClient = 1
  /\ [][Next]_<<requests, allocations, schedule, nextClient>>

THEOREM Spec => []TypeOK

Fairness == 
  WF_vars(Next, <<requests, allocations, schedule, nextClient>>)

THEOREM Spec => Fairness

EventualReturn(client) == 
  <><client \in Clients : requests[client] = {}>_

THEOREM Spec => EventualReturn(c) 

EventualObtainment(client, resource) == 
  <><client \in Clients : resource \in requests[client]>_

THEOREM Spec => EventualObtainment(c, r)

InfinitelyOftenSatisfied(client) == 
  []<><client \in Clients : requests[client] = {}>_

THEOREM Spec => InfinitelyOftenSatisfied(c)
================================================================================