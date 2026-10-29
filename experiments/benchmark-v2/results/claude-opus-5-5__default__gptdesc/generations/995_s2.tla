------------------------ MODULE AllocatorImplementation ------------------------
(******************************************************************************)
(* Resource allocator with explicit client/allocator message passing.         *)
(* Allocator state (unsat, alloc, sched) follows the SchedulingAllocator      *)
(* (inlined here as Sched* definitions so the module is self-contained).      *)
(******************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,
  Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,     \* allocator view: unsatisfied requests per client
  alloc,     \* allocator view: resources allocated to each client
  sched,     \* allocator schedule (sequence of clients)
  requests,  \* client view: pending requests
  holding,   \* client view: resources currently held
  network    \* set of messages in transit

vars == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------------
(* Scheduling allocator (imported allocator state and actions)               *)
-------------------------------------------------------------------------------
Range(f) == { f[x] : x \in DOMAIN f }

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

available == Resources \ (UNION { alloc[c] : c \in Clients })

SchedTypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

SchedInit ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

SchedAllocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

SchedSchedule ==
  LET toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }
  IN  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
      /\ UNCHANGED <<unsat, alloc>>

SchedAllocatorInvariant ==
  /\ \A c \in Clients : unsat[c] \cap alloc[c] = {}
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i, j \in DOMAIN sched : i < j => sched[i] # sched[j]

-------------------------------------------------------------------------------
(* Implementation with messages                                              *)
-------------------------------------------------------------------------------
Messages ==
  [type : {"request", "allocate", "return"},
   clt  : Clients,
   rsrc : SUBSET Resources]

TypeInvariant ==
  /\ SchedTypeInvariant
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding  \in [Clients -> SUBSET Resources]
  /\ network  \in SUBSET Messages

Init ==
  /\ SchedInit
  /\ requests = [c \in Clients |-> {}]
  /\ holding  = [c \in Clients |-> {}]
  /\ network  = {}

\* Client c issues a request: only if nothing pending and nothing held
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* Allocator receives a request message
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator (possibly partially) allocates resources and sends a message
Allocate(c, S) ==
  /\ SchedAllocate(c, S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

\* Client receives an allocation message
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding'  = [holding  EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network'  = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

\* Client returns some held resources (possibly before full satisfaction)
Return(c, S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

\* Allocator receives a return message
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

\* Allocator extends its schedule
Schedule ==
  /\ SchedSchedule
  /\ UNCHANGED <<requests, holding, network>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ \E m \in network : RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)
  /\ \A m \in Messages :
        /\ WF_vars(RReq(m))
        /\ WF_vars(RAlloc(m))
        /\ WF_vars(RRet(m))

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
(* Properties                                                                *)
-------------------------------------------------------------------------------
RequestsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "request" /\ m.clt = c } }

AllocsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "allocate" /\ m.clt = c } }

ReturnsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "return" /\ m.clt = c } }

\* Lower-level invariant relating allocator and client views
Invariant ==
  \A c \in Clients :
     /\ Cardinality(RequestsInTransit(c)) <= 1
     /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c)
                               \cup UNION AllocsInTransit(c)
     /\ alloc[c] = holding[c] \cup UNION AllocsInTransit(c)
                              \cup UNION ReturnsInTransit(c)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {} ~> holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in requests[c]) ~> (r \in holding[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Spec => [](TypeInvariant /\ Invariant /\ ResourceMutex)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
================================================================================