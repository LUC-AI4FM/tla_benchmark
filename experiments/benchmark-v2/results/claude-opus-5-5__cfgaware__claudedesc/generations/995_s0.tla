------------------------ MODULE AllocatorImplementation ------------------------
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS
  Clients,
  Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,
  alloc,
  sched,
  requests,
  holding,
  network

-------------------------------------------------------------------------------
(* Definitions of the underlying scheduling allocator, over unsat, alloc, sched *)

Range(f) == { f[x] : x \in DOMAIN f }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [x \in ss |-> { Append(sq, x) : sq \in perms[ss \ {x}] }]
             IN UNION { ps[x] : x \in ss }
  IN perms[S]

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

schedVars == <<unsat, alloc, sched>>

SchedAllocator ==
  /\ SchedInit
  /\ [][SchedNext]_schedVars
  /\ \A c \in Clients : WF_schedVars(unsat[c] = {} /\ SchedReturn(c, alloc[c]))
  /\ \A c \in Clients : WF_schedVars(\E S \in SUBSET Resources : SchedAllocate(c, S))
  /\ WF_schedVars(SchedSchedule)

-------------------------------------------------------------------------------
(* The implementation *)

Messages ==
  [type : {"request", "allocate", "return"},
   clt  : Clients,
   rsrc : SUBSET Resources]

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}

Request(c, S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {}
  /\ requests' = [requests EXCEPT ![c] = S]
  /\ network' = network \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat, alloc, sched, holding>>

RAlloc(m) ==
  /\ m \in network /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, alloc, sched>>

Return(c) ==
  /\ holding[c] # {}
  /\ holding' = [holding EXCEPT ![c] = {}]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> holding[c]]}
  /\ UNCHANGED <<unsat, alloc, sched, requests>>

RReq(m) ==
  /\ m \in network /\ m.type = "request"
  /\ alloc[m.clt] = {}
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<alloc, sched, requests, holding>>

Allocate(c, S) ==
  /\ SchedAllocate(c, S)
  /\ network' = network \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests, holding>>

RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat, sched, requests, holding>>

Schedule ==
  /\ SchedSchedule
  /\ UNCHANGED <<requests, holding, network>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S) \/ Allocate(c, S)
  \/ \E c \in Clients : Return(c)
  \/ \E m \in network : RReq(m) \/ RAlloc(m) \/ RRet(m)
  \/ Schedule

vars == <<unsat, alloc, sched, requests, holding, network>>

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c] = {} /\ Return(c))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)
  /\ \A m \in Messages :
        /\ WF_vars(RReq(m))
        /\ WF_vars(RAlloc(m))
        /\ WF_vars(RRet(m))

Specification == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------------
(* Properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

RequestsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "request" /\ msg.clt = c } }

AllocsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "allocate" /\ msg.clt = c } }

ReturnsInTransit(c) ==
  { m.rsrc : m \in { msg \in network : msg.type = "return" /\ msg.clt = c } }

Invariant ==
  \A c \in Clients :
    /\ Cardinality(RequestsInTransit(c)) <= 1
    /\ RequestsInTransit(c) # {} =>
          /\ unsat[c] = {}
          /\ AllocsInTransit(c) = {}
          /\ holding[c] = {}
    /\ requests[c] = unsat[c] \cup UNION RequestsInTransit(c)
                              \cup UNION AllocsInTransit(c)
    /\ alloc[c] = holding[c] \cup UNION AllocsInTransit(c)
                             \cup UNION ReturnsInTransit(c)

ClientsWillReceive ==
  \A c \in Clients : requests[c] # {} ~> requests[c] = {}

ClientsWillReturn ==
  \A c \in Clients : holding[c] # {} ~> holding[c] = {}

ClientsWillBeSatisfied ==
  \A c \in Clients : []<>(requests[c] = {})

THEOREM Specification => []TypeInvariant
THEOREM Specification => []ResourceMutex
THEOREM Specification => []Invariant
THEOREM Specification => ClientsWillReceive /\ ClientsWillReturn /\ ClientsWillBeSatisfied
THEOREM Specification => SchedAllocator
================================================================================