------------------------- MODULE AllocatorImplementation -------------------------
(***************************************************************************)
(* Distributed resource allocator.  Clients send requests, the allocator  *)
(* sends (possibly partial) allocations, and clients send returns.  All    *)
(* communication is asynchronous over a network of messages.  Messages may *)
(* be delayed but are never duplicated or corrupted.                       *)
(*                                                                         *)
(* The allocator keeps:                                                    *)
(*   unsat  : the outstanding (unsatisfied) part of each client's request  *)
(*   alloc  : the resources it considers allocated to each client          *)
(*   sched  : the schedule, an ordering of clients to be served            *)
(* The clients keep:                                                       *)
(*   requests : resources the client still waits for                       *)
(*   holding  : resources the client currently holds                       *)
(* The network is the set of messages in transit.                          *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

VARIABLES
  unsat,     \* allocator: unsat[c] = outstanding requests of client c
  alloc,     \* allocator: alloc[c] = resources allocated to client c
  sched,     \* allocator: schedule, a sequence of clients
  requests,  \* client: requests[c] = resources client c still waits for
  holding,   \* client: holding[c] = resources client c currently holds
  network    \* set of messages in transit

vars == <<unsat, alloc, sched, requests, holding, network>>
allocVars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Remove the i-th element of a sequence.
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* The set of all sequences that are permutations of the finite set S.
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

\* Resources not allocated by the allocator to any client.
available == Resources \ (UNION { alloc[c] : c \in Clients })

\* Clients with outstanding requests that are not yet in the schedule.
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

Send(m) == network' = network \cup {m}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract scheduling allocator, stated over the allocator variables.     *)
(* The implementation is required to refine it (property SchedAllocator). *)
(***************************************************************************)

SInit ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

SRequest(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

SAllocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

SReturn(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

SSchedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

SNext ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        SRequest(c, S) \/ SAllocate(c, S) \/ SReturn(c, S)
  \/ SSchedule

SLiveness ==
  /\ \A c \in Clients : WF_allocVars(unsat[c] = {} /\ SReturn(c, alloc[c]))
  /\ \A c \in Clients : WF_allocVars(\E S \in SUBSET Resources : SAllocate(c, S))
  /\ WF_allocVars(SSchedule)

SchedAllocator == SInit /\ [][SNext]_allocVars /\ SLiveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Implementation                                                          *)
(***************************************************************************)

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \subseteq Messages

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

\* Client c issues a request for S: only when nothing outstanding and nothing held.
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ Send([type |-> "request", clt |-> c, rsrc |-> S])
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* Allocator receives a request message.
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ unsat[m.clt] = {} /\ alloc[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator allocates S to c, respecting the schedule; sends a grant.
Allocate(c, S) ==
  /\ SAllocate(c, S)
  /\ Send([type |-> "allocate", clt |-> c, rsrc |-> S])
  /\ UNCHANGED <<requests, holding>>

\* Client receives an allocation message.
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

\* Client returns a nonempty subset of held resources.
Return(c, S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ Send([type |-> "return", clt |-> c, rsrc |-> S])
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

\* Allocator receives a return message.
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

\* Allocator extends the schedule.
Schedule ==
  /\ SSchedule
  /\ UNCHANGED <<requests, holding, network>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ \E m \in network : RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

Liveness ==
  \* clients return everything once their request is fully satisfied
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))
  \* allocator eventually allocates when possible
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  \* allocator eventually schedules waiting clients
  /\ WF_vars(Schedule)
  \* all messages are eventually delivered
  /\ \A m \in Messages :
        /\ WF_vars(RReq(m))
        /\ WF_vars(RAlloc(m))
        /\ WF_vars(RRet(m))

Specification == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

RequestsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "request" /\ msg.clt = c } }

AllocsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "allocate" /\ msg.clt = c } }

ReturnsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "return" /\ msg.clt = c } }

\* Consistency between allocator view, client views, and the network.
Invariant ==
  /\ \A c \in Clients :
       /\ Cardinality(RequestsInTransit(c)) <= 1
       /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c)
                                 \cup UNION AllocsInTransit(c)
       /\ alloc[c] = holding[c] \cup UNION AllocsInTransit(c)
                               \cup UNION ReturnsInTransit(c)
  /\ \A c1, c2 \in Clients : alloc[c1] \cap alloc[c2] # {} => c1 = c2

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {} ~> holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in requests[c] ~> r \in holding[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

AllocatorSchedules ==
  \A c \in Clients : (unsat[c] # {}) ~> (c \in Range(sched) \/ unsat[c] = {})

MessagesDelivered ==
  \A m \in Messages : (m \in network) ~> (m \notin network)

THEOREM Specification => []TypeInvariant
THEOREM Specification => []ResourceMutex
THEOREM Specification => []Invariant
THEOREM Specification => SchedAllocator
THEOREM Specification => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
=============================================================================