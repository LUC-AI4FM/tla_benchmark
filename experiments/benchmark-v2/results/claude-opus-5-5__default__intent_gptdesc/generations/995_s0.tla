----------------------------- MODULE ResourceAllocator -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Clients,     \* finite set of client identifiers
    Resources    \* finite set of reusable resources

ASSUME IsFiniteSet(Clients) /\ IsFiniteSet(Resources)

VARIABLES
    unsat,     \* allocator: unsat[c] = resources requested by c, not yet allocated
    alloc,     \* allocator: alloc[c] = resources the allocator considers allocated to c
    sched,     \* allocator: schedule, i.e. a sequence of clients to be served in order
    requests,  \* client:    requests[c] = resources c still waits for
    holding,   \* client:    holding[c]  = resources c currently holds
    network    \* set of messages in transit

allocVars  == <<unsat, alloc, sched>>
clientVars == <<requests, holding>>
vars       == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------------------
(* Messages and helper operators                                                      *)
-------------------------------------------------------------------------------------
Messages ==
    [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

Range(f) == { f[i] : i \in DOMAIN f }

\* All sequences that enumerate a finite set S exactly once
PermSeqs(S) ==
    { f \in [1..Cardinality(S) -> S] : Range(f) = S }

\* Remove the i-th element of a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* Resources not allocated to anybody
available == Resources \ (UNION { alloc[c] : c \in Clients })

\* Clients with pending requests that are not yet in the schedule
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

\* Message contents in transit, per client and type
InTransit(t, c) == { m.rsrc : m \in { mm \in network : mm.type = t /\ mm.clt = c } }
RequestsInTransit(c) == InTransit("request", c)
AllocsInTransit(c)   == InTransit("allocate", c)
ReturnsInTransit(c)  == InTransit("return", c)

-------------------------------------------------------------------------------------
(* Initial state                                                                      *)
-------------------------------------------------------------------------------------
Init ==
    /\ unsat    = [c \in Clients |-> {}]
    /\ alloc    = [c \in Clients |-> {}]
    /\ sched    = << >>
    /\ requests = [c \in Clients |-> {}]
    /\ holding  = [c \in Clients |-> {}]
    /\ network  = {}

-------------------------------------------------------------------------------------
(* Client actions                                                                     *)
-------------------------------------------------------------------------------------
\* A client with no outstanding request and no held resources issues a new request.
Request(c, S) ==
    /\ requests[c] = {}
    /\ holding[c] = {}
    /\ S # {}
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ network'  = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
    /\ UNCHANGED <<allocVars, holding>>

\* A client receives an (possibly partial) allocation message.
Rsp(c) ==
    \E m \in network :
        /\ m.type = "allocate"
        /\ m.clt = c
        /\ holding'  = [holding EXCEPT ![c] = @ \cup m.rsrc]
        /\ requests' = [requests EXCEPT ![c] = @ \ m.rsrc]
        /\ network'  = network \ {m}
        /\ UNCHANGED allocVars

\* A client returns a nonempty subset of the resources it holds.
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq holding[c]
    /\ holding' = [holding EXCEPT ![c] = @ \ S]
    /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
    /\ UNCHANGED <<allocVars, requests>>

-------------------------------------------------------------------------------------
(* Allocator actions                                                                  *)
-------------------------------------------------------------------------------------
\* The allocator receives a request message. It only handles the request once all
\* previously allocated resources of that client have been returned.
RReq(c) ==
    \E m \in network :
        /\ m.type = "request"
        /\ m.clt = c
        /\ alloc[c] = {}
        /\ unsat'   = [unsat EXCEPT ![c] = m.rsrc]
        /\ network' = network \ {m}
        /\ UNCHANGED <<alloc, sched, clientVars>>

\* The allocator receives a return message.
RRet(c) ==
    \E m \in network :
        /\ m.type = "return"
        /\ m.clt = c
        /\ alloc'   = [alloc EXCEPT ![c] = @ \ m.rsrc]
        /\ network' = network \ {m}
        /\ UNCHANGED <<unsat, sched, clientVars>>

\* The allocator allocates a set S of available resources to a scheduled client c,
\* provided no client earlier in the schedule claims any resource of S.
\* A fully satisfied client is removed from the schedule.
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available \cap unsat[c]
    /\ \E i \in DOMAIN sched :
          /\ sched[i] = c
          /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
          /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
    /\ alloc'   = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat'   = [unsat EXCEPT ![c] = @ \ S]
    /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
    /\ UNCHANGED clientVars

\* The allocator extends the schedule by some ordering of the waiting clients.
Schedule ==
    /\ toSchedule # {}
    /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
    /\ UNCHANGED <<unsat, alloc, clientVars, network>>

-------------------------------------------------------------------------------------
(* Next-state relation and specification                                              *)
-------------------------------------------------------------------------------------
Next ==
    \/ \E c \in Clients, S \in SUBSET Resources :
          Request(c, S) \/ Return(c, S) \/ Allocate(c, S)
    \/ \E c \in Clients : Rsp(c) \/ RReq(c) \/ RRet(c)
    \/ Schedule

Fairness ==
    \* clients eventually return held resources once their request is satisfied
    /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))
    \* message delivery: every message in transit is eventually received
    /\ \A c \in Clients : WF_vars(Rsp(c))
    /\ \A c \in Clients : WF_vars(RReq(c))
    /\ \A c \in Clients : WF_vars(RRet(c))
    \* allocator eventually issues allocations when (repeatedly) possible
    /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))
    \* allocator eventually schedules waiting clients
    /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------------
(* Safety properties                                                                  *)
-------------------------------------------------------------------------------------
TypeOK ==
    /\ unsat    \in [Clients -> SUBSET Resources]
    /\ alloc    \in [Clients -> SUBSET Resources]
    /\ sched    \in Seq(Clients)
    /\ requests \in [Clients -> SUBSET Resources]
    /\ holding  \in [Clients -> SUBSET Resources]
    /\ network  \subseteq Messages

\* No two distinct clients ever hold the same resource
Mutex ==
    \A c1, c2 \in Clients :
        c1 # c2 => holding[c1] \cap holding[c2] = {}

\* The allocator never allocates the same resource to two distinct clients
AllocMutex ==
    \A c1, c2 \in Clients :
        c1 # c2 => alloc[c1] \cap alloc[c2] = {}

\* Consistency of allocator and client views modulo messages in transit
NetworkConsistency ==
    \A c \in Clients :
        /\ Cardinality(RequestsInTransit(c)) <= 1
        /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c)
                                  \cup UNION AllocsInTransit(c)
        /\ alloc[c] = holding[c] \cup UNION AllocsInTransit(c)
                                 \cup UNION ReturnsInTransit(c)
        /\ RequestsInTransit(c) # {} =>
              /\ unsat[c] = {}
              /\ AllocsInTransit(c) = {}
        /\ holding[c] \subseteq alloc[c]
        /\ unsat[c] \subseteq requests[c]

\* Well-formedness of the schedule
ScheduleInv ==
    /\ \A i, j \in DOMAIN sched : i # j => sched[i] # sched[j]
    /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
    /\ \A c \in Clients : unsat[c] # {} => (c \in Range(sched) \/ c \in toSchedule)

Invariant ==
    /\ TypeOK
    /\ Mutex
    /\ AllocMutex
    /\ NetworkConsistency
    /\ ScheduleInv

-------------------------------------------------------------------------------------
(* Liveness properties                                                                *)
-------------------------------------------------------------------------------------
\* A client whose request is fully satisfied eventually returns everything it holds
ClientsWillReturn ==
    \A c \in Clients : (requests[c] = {}) ~> (holding[c] = {})

\* Every requested resource is eventually obtained by the requesting client
ClientsWillObtain ==
    \A c \in Clients, r \in Resources :
        (r \in requests[c]) ~> (r \in holding[c])

\* Every client's request is satisfied infinitely often
InfOftenSatisfied ==
    \A c \in Clients : []<>(requests[c] = {})

\* Waiting clients are eventually scheduled
WaitingClientsScheduled ==
    \A c \in Clients :
        (unsat[c] # {}) ~> (c \in Range(sched) \/ unsat[c] = {})

\* Pending resources are eventually allocated by the allocator
AllocatorWillAllocate ==
    \A c \in Clients, r \in Resources :
        (r \in unsat[c]) ~> (r \in alloc[c])

\* Every message sent is eventually delivered
MessagesDelivered ==
    \A m \in Messages : (m \in network) ~> (m \notin network)

-------------------------------------------------------------------------------------
THEOREM Spec => []Invariant
THEOREM Spec => ClientsWillReturn
THEOREM Spec => ClientsWillObtain
THEOREM Spec => InfOftenSatisfied
THEOREM Spec => WaitingClientsScheduled
THEOREM Spec => AllocatorWillAllocate
THEOREM Spec => MessagesDelivered
=====================================================================================