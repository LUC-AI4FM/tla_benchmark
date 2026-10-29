------------------------- MODULE AllocatorImplementation -------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,      \* allocator's view: unsat[c] = resources requested by c, not yet allocated
  alloc,      \* allocator's view: alloc[c] = resources allocated to c, not yet returned
  sched,      \* allocator's schedule of pending clients
  requests,   \* client's view: requests[c] = resources c is still waiting for
  holding,    \* client's view: holding[c] = resources c currently holds
  network     \* set of messages in transit (unordered)

vars == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------------
Range(f) == {f[x] : x \in DOMAIN f}

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

PermSeqs(S) == {sq \in [1..Cardinality(S) -> S] : Range(sq) = S}

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

available == Resources \ (UNION {alloc[c] : c \in Clients})

toSchedule == {c \in Clients : unsat[c] # {} /\ c \notin Range(sched)}

TypeOK ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \subseteq Messages

-------------------------------------------------------------------------------
Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = <<>>
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

\* Client c sends a request for a non-empty set S of resources.
Request(c, S) ==
  /\ requests[c] = {}
  /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* Allocator receives a request message.
RReq(m) ==
  /\ m \in network
  /\ m.type = "request"
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator appends pending, unscheduled clients to the schedule.
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc, requests, holding, network>>

\* Allocator allocates a set S of available resources to client c,
\* respecting schedule order.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
       /\ sched[i] = c
       /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
       /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

\* Client receives an allocate message.
RAlloc(m) ==
  /\ m \in network
  /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

\* Client c returns a non-empty set S of resources it holds.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

\* Allocator receives a return message.
RRet(m) ==
  /\ m \in network
  /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ \E m \in network : RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

-------------------------------------------------------------------------------
\* Fairness conditions

\* Fair delivery of messages of each kind for each client.
RReqFor(c)   == \E m \in network : m.clt = c /\ RReq(m)
RAllocFor(c) == \E m \in network : m.clt = c /\ RAlloc(m)
RRetFor(c)   == \E m \in network : m.clt = c /\ RRet(m)

Liveness ==
  /\ \A c \in Clients : WF_vars(RReqFor(c))
  /\ \A c \in Clients : WF_vars(RAllocFor(c))
  /\ \A c \in Clients : WF_vars(RRetFor(c))
  /\ WF_vars(Schedule)
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
\* Safety

Mutex ==
  \A c1, c2 \in Clients :
    c1 # c2 => /\ holding[c1] \cap holding[c2] = {}
               /\ alloc[c1] \cap alloc[c2] = {}

ClientHoldsOnlyAllocated ==
  \A c \in Clients : holding[c] \subseteq alloc[c]

\* Liveness properties

ClientsWillObtain ==
  \A c \in Clients : (requests[c] # {}) ~> (requests[c] = {})

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {}) ~> (holding[c] = {})

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Spec => [](TypeOK /\ Mutex /\ ClientHoldsOnlyAllocated)
THEOREM Spec => ClientsWillObtain /\ ClientsWillReturn /\ InfOftenSatisfied
================================================================================