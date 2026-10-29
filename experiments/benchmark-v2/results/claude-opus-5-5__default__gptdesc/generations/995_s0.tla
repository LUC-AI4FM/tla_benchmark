------------------------- MODULE ImplementingAllocator -------------------------
(***************************************************************************)
(* Resource allocator with explicit message passing between clients and   *)
(* the allocator. The allocator state (unsat, alloc, sched) follows the   *)
(* scheduling allocator; client state (requests, holding) and the network *)
(* of in-transit messages are added here.                                 *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,     \* unsat[c]   : resources requested by c, not yet allocated (allocator view)
  alloc,     \* alloc[c]   : resources allocated to c (allocator view)
  sched,     \* sequence of clients scheduled for allocation
  requests,  \* requests[c]: resources c is still waiting for (client view)
  holding,   \* holding[c] : resources c currently holds (client view)
  network    \* set of in-transit messages

Sched == INSTANCE Naturals  \* placeholder-free: allocator state is defined below

vars == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------------
(* Auxiliary definitions (as in the scheduling allocator)                    *)

Range(f) == { f[x] : x \in DOMAIN f }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                         { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

available == Resources \ (UNION {alloc[c] : c \in Clients})

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

-------------------------------------------------------------------------------
TypeInvariant ==
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
  /\ sched = << >>
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

(* Client c requests set S; only when it has no pending request and holds nothing. *)
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

(* Allocator receives a request message. *)
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {} /\ unsat[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

(* Allocator schedules clients with pending requests. *)
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc, requests, holding, network>>

(* Allocator (possibly partially) allocates S to client c and sends a message. *)
Allocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
       /\ sched[i] = c
       /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
       /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

(* Client receives an allocation message. *)
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

(* Client returns held resources, possibly before its request is fully satisfied. *)
Return(c, S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

(* Allocator receives a return message. *)
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ \E m \in network : RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients :
        WF_vars(requests[c] = {} /\ Return(c, holding[c]))
  /\ \A c \in Clients :
        WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)
  /\ \A m \in Messages :
        /\ WF_vars(RReq(m))
        /\ WF_vars(RAlloc(m))
        /\ WF_vars(RRet(m))

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
(* Lower-level invariant relating allocator and client views *)

RequestsInTransit(c) ==
  { m.rsrc : m \in { mm \in network : mm.type = "request" /\ mm.clt = c } }
AllocsInTransit(c) ==
  { m.rsrc : m \in { mm \in network : mm.type = "allocate" /\ mm.clt = c } }
ReturnsInTransit(c) ==
  { m.rsrc : m \in { mm \in network : mm.type = "return" /\ mm.clt = c } }

Invariant ==
  \A c \in Clients :
     /\ Cardinality(RequestsInTransit(c)) <= 1
     /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c)
                                \cup UNION AllocsInTransit(c)
     /\ alloc[c] = holding[c] \cup UNION AllocsInTransit(c)
                              \cup UNION ReturnsInTransit(c)
     /\ unsat[c] \cap alloc[c] = {}
     /\ (RequestsInTransit(c) # {}) => (unsat[c] = {})

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

-------------------------------------------------------------------------------
(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {}) ~> (holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in requests[c]) ~> (r \in holding[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

-------------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Invariant /\ ResourceMutex)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
================================================================================