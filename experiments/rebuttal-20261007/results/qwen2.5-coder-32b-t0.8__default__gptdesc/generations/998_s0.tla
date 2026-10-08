---- MODULE ResourceAllocator ----

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Clients, Resources, Schedule
ASSUME Clients \in FinSet
ASSUME Resources \in FinSet
ASSUME Schedule \in Seq(Power(Clients))

VARIABLES allocations, requests, returns

Init == 
  /\ allocations = [client \in Clients |-> {}]
  /\ requests = [client \in Clients |-> {}]
  /\ returns = [resource \in Resources |-> {}]

Next ==
  \/ \E client \in Clients : ~(\exists res \in requests[client] : res \notin allocations[client])
     /\ requests[client] = {}
     /\ \E res \in Resources \ (allocations[\E cl \in Clients : res \in allocations[cl]]) :
        \/ allocations' = [allocations EXCEPT ![client] = allocations[client] \cup {res}]
        /\ requests' = [requests EXCEPT ![client] = requests[client]]
        /\ returns' = returns
  \/ \E client \in Clients, resource \in allocations[client] :
     ~(\exists res \in requests[client] : res \notin allocations[client])
     /\ allocations' = [allocations EXCEPT ![client] = allocations[client] \ {resource}]
     /\ requests' = [requests EXCEPT ![client] = requests[client]]
     /\ returns' = [returns EXCEPT ![resource] = returns[resource] \cup {client}]
  \/ \E i \in DOMAIN Schedule, client \in Schedule[i] :
     ~(\exists res \in requests[client] : res \notin allocations[client])
     /\ requests'[client] = requests[client] \cup (Resources \ allocations[client])
     /\ allocations' = allocations
     /\ returns' = returns

Spec ==
  Init /\ [][Next]_<<allocations, requests, returns>> /\ WF_next(Next)

MutualExclusion ==
  \A res \in Resources : Cardinality({cl \in Clients : res \in allocations[cl]}) <= 1

AllocatorInvariant ==
  \A cl \in Clients : requests[cl] = {} \/ (\E res \in requests[cl] : res \notin allocations[cl])

ClientReturnsResources ==
  WF_next(\E client \in Clients : ~(\exists res \in requests[client] : res \notin allocations[client])
           /\ allocations[client] /= {}
           -> \A resource \in allocations[client] :
                 returns[resource] = {client})

AllocationsEventuallyHappen ==
  SF_next(\E i \in DOMAIN Schedule, client \in Schedule[i] :
            ~(\exists res \in requests[client] : res \notin allocations[client])
            /\ requests[client] /= {})

SchedulingEventuallyOccurs ==
  SF_next(\E i \in DOMAIN Schedule :
            \A client \in Schedule[i] :
              ~(\exists res \in requests[client] : res \notin allocations[client])
              /\ requests[client] /= {})

EventualReturn ==
  WF_next(\E client \in Clients, resource \in allocations[client] :
            returns[resource] = {client})

EventualObtainment ==
  SF_next(\E client \in Clients :
            ~(\exists res \in requests[client] : res \notin allocations[client])
            /\ requests[client] /= {}
            -> \A res \in requests[client] :
                 allocations[cl] = allocations[cl] \cup {res})

InfinitelyOftenSatisfied ==
  WF_next(\E client \in Clients, resource \in allocations[client] :
              requests[client] = {})

THEOREM Spec => [](MutualExclusion /\ AllocatorInvariant)
THEOREM Spec => ClientReturnsResources
THEOREM Spec => AllocationsEventuallyHappen
THEOREM Spec => SchedulingEventuallyOccurs
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfied

====