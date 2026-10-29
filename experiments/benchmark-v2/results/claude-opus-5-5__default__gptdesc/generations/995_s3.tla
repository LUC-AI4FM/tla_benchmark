------------------------ MODULE AllocatorImplementation ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* allocator view: unsat[c] = resources c still waits for
  alloc,       \* allocator view: alloc[c] = resources allocated to c
  sched,       \* allocator schedule: sequence of clients
  requests,    \* client view: requests[c] = resources c still waits for
  holding,     \* client view: holding[c] = resources c currently holds
  network      \* set of messages in transit

-------------------------------------------------------------------------------
(* Scheduling allocator (allocator-side state and actions)                    *)

Range(f) == { f[x] : x \in DOMAIN f }

PermSeqs(S) ==
  { f \in [1..Cardinality(S) -> S] :
      \A i, j \in DOMAIN f : i # j => f[i] # f[j] }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

available == Resources \ (UNION { alloc[c] : c \in Clients })

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

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
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

-------------------------------------------------------------------------------
(* Messages and full state                                                    *)

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

vars == <<unsat, alloc, sched, requests, holding, network>>

TypeInvariant ==
  /\ SchedTypeInvariant
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages

Init ==
  /\ SchedInit
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

-------------------------------------------------------------------------------
(* Client actions                                                             *)

\* A client with no pending requests and no held resources issues a request.
Request(c, S) ==
  /\ requests[c] = {}
  /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* A client receives an (possibly partial) allocation message.
Response(c, S) ==
  LET m == [type |-> "allocate", clt |-> c, rsrc |-> S]
  IN  /\ m \in network
      /\ holding' = [holding EXCEPT ![c] = @ \cup S]
      /\ requests' = [requests EXCEPT ![c] = @ \ S]
      /\ network' = network \ {m}
      /\ UNCHANGED <<unsat, alloc, sched>>

\* A client returns some held resources (possibly before full satisfaction).
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

-------------------------------------------------------------------------------
(* Allocator actions                                                          *)

\* Allocator receives a request message from client c.
RReq(c) ==
  \E m \in network :
    /\ m.type = "request"
    /\ m.clt = c
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = m.rsrc]
    /\ network' = network \ {m}
    /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator allocates resources to client c and sends a message.
RAlloc(c) ==
  \E S \in SUBSET Resources :
    /\ SchedAllocate(c, S)
    /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
    /\ UNCHANGED <<requests, holding>>

\* Allocator receives a return message from client c.
RRet(c) ==
  \E m \in network :
    /\ m.type = "return"
    /\ m.clt = c
    /\ alloc' = [alloc EXCEPT ![c] = @ \ m.rsrc]
    /\ network' = network \ {m}
    /\ UNCHANGED <<unsat, sched, requests, holding>>

\* Allocator extends its schedule.
Schedule ==
  /\ SchedSchedule
  /\ UNCHANGED <<requests, holding, network>>

-------------------------------------------------------------------------------

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
       Request(c, S) \/ Response(c, S) \/ Return(c, S)
  \/ \E c \in Clients : RReq(c) \/ RAlloc(c) \/ RRet(c)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ holding[c] # {}
                                  /\ Return(c, holding[c]))
  /\ \A c \in Clients : WF_vars(RReq(c))
  /\ \A c \in Clients : WF_vars(RAlloc(c))
  /\ \A c \in Clients : WF_vars(RRet(c))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Response(c, S))
  /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
(* Properties                                                                 *)

RequestsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "request" /\ msg.clt = c } }

AllocsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "allocate" /\ msg.clt = c } }

ReturnsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "return" /\ msg.clt = c } }

\* Lower-level invariant relating allocator and client views.
Invariant ==
  \A c \in Clients :
    /\ Cardinality(RequestsInTransit(c)) <= 1
    /\ requests[c] = unsat[c]
                     \cup UNION RequestsInTransit(c)
                     \cup UNION AllocsInTransit(c)
    /\ alloc[c] = holding[c]
                  \cup UNION AllocsInTransit(c)
                  \cup UNION ReturnsInTransit(c)

\* No resource is held by two different clients.
ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

\* Clients whose requests are satisfied eventually return their resources.
ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {}) ~> (holding[c] = {})

\* Every requested resource is eventually obtained.
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in requests[c]) ~> (r \in holding[c])

\* Every client's requests are infinitely often fully satisfied.
InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Spec => [](TypeInvariant /\ Invariant /\ ResourceMutex)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
================================================================================