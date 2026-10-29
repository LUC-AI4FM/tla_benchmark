------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c] denotes the outstanding requests of client c
  alloc,       \* alloc[c] denotes the resources allocated to client c
  sched        \* schedule represented as a sequence of clients

vars == <<unsat, alloc, sched>>

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

-----------------------------------------------------------------------------

Range(f) == { f[x] : x \in DOMAIN f }

\* Resources that are not currently allocated to any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* The set of permutations of a finite set, represented as sequences
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the i-th element from a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* Clients with pending requests that have not yet been scheduled
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

-----------------------------------------------------------------------------

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

\* A client may request resources only if it has no outstanding
\* unsatisfied request and currently holds no resources.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

\* Allocation of a (possibly partial) set of available resources to a
\* scheduled client, provided no client earlier in the schedule
\* still requires any of these resources.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* A client may return resources (possibly early) at any time.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

\* Append the clients with pending, unscheduled requests to the schedule
\* in some arbitrary order.
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

Allocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Spec == Allocator

-----------------------------------------------------------------------------
\* Safety properties

ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients == Clients \ Range(sched)

\* Resources that may be held by or requested by clients up to position i
\* in the schedule, or held by unscheduled clients
PrevResources(i) ==
       unsat[sched[i]] \cup alloc[sched[i]]
  \cup UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) }
  \cup UNION { alloc[c] : c \in UnscheduledClients }

AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) : sched[i] # sched[j]
  /\ \A c \in toSchedule : alloc[c] = {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) :
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

-----------------------------------------------------------------------------
\* Liveness properties

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------

THEOREM Allocator => []TypeInvariant
THEOREM Allocator => []ResourceMutex
THEOREM Allocator => []AllocatorInvariant
THEOREM Allocator => ClientsWillReturn
THEOREM Allocator => ClientsWillObtain
THEOREM Allocator => InfOftenSatisfied

=============================================================================