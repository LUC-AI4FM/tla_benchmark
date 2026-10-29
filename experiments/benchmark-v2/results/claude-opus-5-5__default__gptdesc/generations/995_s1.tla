---------------------- MODULE AllocatorImplementation ----------------------
(***************************************************************************)
(* Resource allocator with explicit message passing between clients and   *)
(* the allocator. The allocator's state (unsat, alloc, sched) follows a   *)
(* scheduling allocator, defined inline below with the prefix "Sched_".   *)
(* Clients keep local state (requests, holding). Messages in transit are  *)
(* kept in the set network.                                               *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

VARIABLES
  unsat,     \* allocator view: outstanding (unsatisfied) requests per client
  alloc,     \* allocator view: resources allocated to each client
  sched,     \* allocator: schedule of clients (sequence)
  requests,  \* client view: resources the client still waits for
  holding,   \* client view: resources the client currently holds
  network    \* set of messages in transit

vars == <<unsat, alloc, sched, requests, holding, network>>

-------------------------------------------------------------------------
(*************************** Scheduling allocator ***************************)

Range(f) == { f[x] : x \in DOMAIN f }

Sched_TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

Sched_available == Resources \ (UNION { alloc[c] : c \in Clients })

Sched_Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

Sched_toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN UNION { ps[x] : x \in ss }
  IN perms[S]

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

Sched_Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq Sched_available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

Sched_Schedule ==
  /\ Sched_toSchedule # {}
  /\ \E sq \in PermSeqs(Sched_toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Sched_AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) : sched[i] # sched[j]
  /\ \A c \in Clients : unsat[c] # {} => c \in Range(sched) \/ c \in Sched_toSchedule

-------------------------------------------------------------------------
(****************************** Implementation *****************************)

Messages ==
  [type : {"request", "allocate", "return"},
   clt  : Clients,
   rsrc : SUBSET Resources]

TypeInvariant ==
  /\ Sched_TypeInvariant
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding  \in [Clients -> SUBSET Resources]
  /\ network  \in SUBSET Messages

Init ==
  /\ Sched_Init
  /\ requests = [c \in Clients |-> {}]
  /\ holding  = [c \in Clients |-> {}]
  /\ network  = {}

\* Client c requests set S: only when it has no pending request and holds nothing.
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* Client c receives a (possibly partial) allocation message.
Rsp(c) ==
  /\ \E m \in network :
        /\ m.type = "allocate" /\ m.clt = c
        /\ holding'  = [holding  EXCEPT ![c] = @ \cup m.rsrc]
        /\ requests' = [requests EXCEPT ![c] = @ \ m.rsrc]
        /\ network'  = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

\* Client c returns resources, possibly before its request is fully satisfied.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

\* Allocator receives a request message.
RReq(m) ==
  /\ m \in network
  /\ m.type = "request"
  /\ alloc[m.clt] = {}   \* do not handle requests prematurely
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator allocates resources and sends an allocation message.
Allocate(c, S) ==
  /\ Sched_Allocate(c, S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

\* Allocator extends its schedule.
Schedule ==
  /\ Sched_Schedule
  /\ UNCHANGED <<requests, holding, network>>

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
  \/ \E c \in Clients : Rsp(c)
  \/ \E m \in network : RReq(m) \/ RRet(m)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c, holding[c]))
  /\ \A c \in Clients : WF_vars(Rsp(c))
  /\ \A m \in Messages : WF_vars(RReq(m))
  /\ \A m \in Messages : WF_vars(RRet(m))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------
(******************************** Properties *******************************)

RequestsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "request" /\ msg.clt = c } }

AllocsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "allocate" /\ msg.clt = c } }

ReturnsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "return" /\ msg.clt = c } }

\* Lower-level invariant relating the allocator's and the clients' views.
Invariant ==
  /\ Sched_AllocatorInvariant
  /\ \A c \in Clients :
       /\ Cardinality(RequestsInTransit(c)) <= 1
       /\ RequestsInTransit(c) # {} =>
             /\ unsat[c] = {}
             /\ holding[c] = {}
             /\ AllocsInTransit(c) = {}
       /\ requests[c] = unsat[c] \cup (UNION AllocsInTransit(c))
                                  \cup (UNION RequestsInTransit(c))
       /\ alloc[c] = holding[c] \cup (UNION AllocsInTransit(c))
                                \cup (UNION ReturnsInTransit(c))

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {}) ~> (holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in requests[c]) ~> (r \in holding[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Spec => [](TypeInvariant /\ Invariant /\ ResourceMutex)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
=============================================================================