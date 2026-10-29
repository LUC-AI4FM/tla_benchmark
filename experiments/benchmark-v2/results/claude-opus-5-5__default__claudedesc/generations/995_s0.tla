------------------------ MODULE AllocatorImplementation ------------------------
(***************************************************************************)
(* Implementation of the scheduling allocator with explicit client-side     *)
(* state and an asynchronous network between clients and the allocator.    *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  (** variables held by the allocator **)
  unsat,       \* set of all outstanding requests per process
  alloc,       \* set of resources allocated to given process
  sched,       \* schedule represented as a sequence of clients
  (** variables of the clients **)
  requests,    \* pending requests per client
  holding,     \* resources currently held by the client
  (** communication network between clients and allocator **)
  network      \* set of messages in transit

Sched == INSTANCE SchedulingAllocator

-------------------------------------------------------------------------------

Messages ==
  [type : {"request", "allocate", "return"},
   clt  : Clients,
   rsrc : SUBSET Resources]

TypeInvariant ==
  /\ Sched!TypeInvariant
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages

-------------------------------------------------------------------------------

(* Initially, no resources have been requested or allocated. *)
Init ==
  /\ Sched!Init
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

(* A client c may request a set of resources provided that it has      *)
(* neither pending requests nor holds any resources.                   *)
Request(c,S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {} /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

(* Reception of a request message by the allocator. *)
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {}   \* don't handle requests until previous return is complete
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

(* Allocation of a set of available resources to a client that has     *)
(* requested them, following the schedule order.                       *)
Allocate(c,S) ==
  /\ Sched!Allocate(c,S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

(* Reception of an allocation message by a client. *)
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

(* Client c returns a set of resources that it holds. It may do so     *)
(* even before its full request has been honored.                      *)
Return(c,S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

(* Reception of a return message by the allocator. *)
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

(* The allocator extends its schedule by adding processes with          *)
(* outstanding requests.                                                *)
Schedule ==
  /\ Sched!Schedule
  /\ UNCHANGED <<requests, holding, network>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
  \/ \E m \in network :
        RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

vars == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------------

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c,S))
  /\ WF_vars(Schedule)
  /\ \A m \in Messages :
        /\ WF_vars(RReq(m))
        /\ WF_vars(RAlloc(m))
        /\ WF_vars(RRet(m))

Specification == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------

(* Safety properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

RequestsInTransit(c) ==
  { msg.rsrc : msg \in {m \in network : m.type = "request" /\ m.clt = c} }

AllocsInTransit(c) ==
  { msg.rsrc : msg \in {m \in network : m.type = "allocate" /\ m.clt = c} }

ReturnsInTransit(c) ==
  { msg.rsrc : msg \in {m \in network : m.type = "return" /\ m.clt = c} }

Invariant ==
  \A c \in Clients :
     /\ Cardinality(RequestsInTransit(c)) <= 1
     /\ requests[c] = unsat[c]
                      \cup UNION RequestsInTransit(c)
                      \cup UNION AllocsInTransit(c)
     /\ alloc[c] = holding[c]
                   \cup UNION AllocsInTransit(c)
                   \cup UNION ReturnsInTransit(c)
     /\ RequestsInTransit(c) # {} => /\ unsat[c] = {}
                                     /\ AllocsInTransit(c) = {}
     /\ \A S \in AllocsInTransit(c) : S # {}
     /\ \A S \in ReturnsInTransit(c) : S # {}

(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {} ~> holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in requests[c] ~> r \in holding[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

-------------------------------------------------------------------------------

THEOREM Specification => []TypeInvariant
THEOREM Specification => []ResourceMutex
THEOREM Specification => []Invariant
THEOREM Specification => ClientsWillReturn
THEOREM Specification => ClientsWillObtain
THEOREM Specification => InfOftenSatisfied

(* The implementation refines the scheduling allocator. *)
SchedAllocator == Sched!Allocator

THEOREM Specification => SchedAllocator
================================================================================