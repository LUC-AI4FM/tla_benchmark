------------------------ MODULE AllocatorImplementation ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,
  Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat, alloc, sched,
  requests, holding,
  network

-------------------------------------------------------------------------------
(* Scheduling allocator: high-level allocator state and behavior.               *)
-------------------------------------------------------------------------------

Range(f) == { f[x] : x \in DOMAIN f }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

SchedTypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

available == Resources \ (UNION { alloc[c] : c \in Clients })

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

SchedVars == <<unsat, alloc, sched>>

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
        /\ \A j \in 1 .. i-1 : unsat[sched[j]] \cap S = {}
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
  /\ [][SchedNext]_SchedVars
  /\ \A c \in Clients : WF_SchedVars(unsat[c] = {} /\ SchedReturn(c, alloc[c]))
  /\ \A c \in Clients : WF_SchedVars(\E S \in SUBSET Resources : SchedAllocate(c, S))
  /\ WF_SchedVars(SchedSchedule)

-------------------------------------------------------------------------------
(* Implementation with clients and message passing.                            *)
-------------------------------------------------------------------------------

Messages ==
  [type : {"request", "allocate", "return"}, clt : Clients, rsrc : SUBSET Resources]

TypeInvariant ==
  /\ SchedTypeInvariant
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages

vars == <<unsat, alloc, sched, requests, holding, network>>

Init ==
  /\ SchedInit
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

\* Client c issues a request for resources S.
Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

\* Allocator handles a request message.
RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {}   \* do not handle request before returns arrive
  /\ unsat[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

\* Allocator allocates (possibly partially) resources S to client c.
Allocate(c, S) ==
  /\ SchedAllocate(c, S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

\* Client receives an allocation message.
RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

\* Client c returns resources S it holds.
Return(c, S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

\* Allocator receives a return message.
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

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
        WF_vars(RReq(m)) /\ WF_vars(RAlloc(m)) /\ WF_vars(RRet(m))

Specification == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------

RequestsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "request" /\ m.clt = c } }

AllocsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "allocate" /\ m.clt = c } }

ReturnsInTransit(c) ==
  { msg.rsrc : msg \in { m \in network : m.type = "return" /\ m.clt = c } }

Invariant ==
  \A c \in Clients :
    /\ Cardinality(RequestsInTransit(c)) <= 1
    /\ requests[c] = unsat[c]
                     \cup UNION RequestsInTransit(c)
                     \cup UNION AllocsInTransit(c)
    /\ alloc[c] = holding[c]
                  \cup UNION AllocsInTransit(c)
                  \cup UNION ReturnsInTransit(c)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

ClientsWillReturn ==
  \A c \in Clients : (requests[c] = {} ~> holding[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in requests[c] ~> r \in holding[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

===============================================================================