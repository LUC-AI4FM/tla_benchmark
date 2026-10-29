------------------------------ MODULE AllocatorImplementation ------------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,     \* allocator's view: unsat[c] = resources outstanding for client c
  alloc,     \* allocator's view: alloc[c] = resources allocated to client c
  sched,     \* allocator's schedule of pending clients
  requests,  \* client's view: requests[c] = resources still requested by c
  holding,   \* client's view: holding[c] = resources currently held by c
  network    \* set of messages in transit

vars == <<unsat, alloc, sched, requests, holding, network>>
schedVars == <<unsat, alloc, sched>>

-------------------------------------------------------------------------------------------
(* Auxiliary operators *)

Range(f) == { f[x] : x \in DOMAIN f }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |-> { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

-------------------------------------------------------------------------------------------
(* The high-level scheduling allocator, stated over unsat, alloc, sched *)

available == Resources \ (UNION { alloc[c] : c \in Clients })

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

SchedInit ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

SchedRequest(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

SchedAllocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

SchedReturn(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

SchedSchedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

SchedNext ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        SchedRequest(c, S) \/ SchedAllocate(c, S) \/ SchedReturn(c, S)
  \/ SchedSchedule

SchedAllocator ==
  /\ SchedInit
  /\ [][SchedNext]_schedVars
  /\ \A c \in Clients : WF_schedVars(unsat[c] = {} /\ SchedReturn(c, alloc[c]))
  /\ \A c \in Clients : WF_schedVars(\E S \in SUBSET Resources : SchedAllocate(c, S))
  /\ WF_schedVars(SchedSchedule)

-------------------------------------------------------------------------------------------
(* The distributed implementation *)

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages

Init ==
  /\ SchedInit
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

(* Client c requests set S of resources *)
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

(* Allocator receives a request message *)
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {}   \* wait until earlier returns have been processed
  /\ unsat[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

(* Allocator allocates resources S to client c *)
Allocate(c, S) ==
  /\ SchedAllocate(c, S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

(* Client receives an allocation message *)
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

(* Client c returns resources S *)
Return(c, S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

(* Allocator receives a return message *)
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

(* Allocator extends its schedule *)
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

Specification == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------------------
(* Correctness properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

RequestsInTransit(c) ==
  { m.rsrc : m \in { mm \in network : mm.type = "request" /\ mm.clt = c } }

AllocsInTransit(c) ==
  UNION { m.rsrc : m \in { mm \in network : mm.type = "allocate" /\ mm.clt = c } }

ReturnsInTransit(c) ==
  UNION { m.rsrc : m \in { mm \in network : mm.type = "return" /\ mm.clt = c } }

Invariant ==
  \A c \in Clients :
    /\ Cardinality(RequestsInTransit(c)) <= 1
    /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c) \cup AllocsInTransit(c)
    /\ alloc[c] = holding[c] \cup AllocsInTransit(c) \cup ReturnsInTransit(c)

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {} ~> holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in requests[c] ~> r \in holding[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Specification => [](TypeInvariant /\ ResourceMutex /\ Invariant)
THEOREM Specification => SchedAllocator
THEOREM Specification => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
=============================================================================================