---------------------- MODULE SchedulingAllocator ----------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,  \* unsat[c] = set of outstanding (unsatisfied) requests of client c
  alloc,  \* alloc[c] = set of resources currently allocated to client c
  sched   \* sequence of clients: the current allocation schedule

vars == <<unsat, alloc, sched>>

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

-------------------------------------------------------------------------

\* Resources not currently held by any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of elements appearing in a sequence (or range of a function)
Range(f) == { f[x] : x \in DOMAIN f }

\* Set of all permutations (as sequences) of the elements of a finite set S
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the i-th element from a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* Clients with pending requests that are not yet scheduled
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

-------------------------------------------------------------------------

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

\* A client with no pending requests and no held resources issues a request.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

\* Allocate a set of available, requested resources to a scheduled client,
\* provided no client earlier in the schedule has requested any of them.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* A client returns some of the resources it holds.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

\* Append a permutation of all unscheduled clients with pending requests.
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

-------------------------------------------------------------------------

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients == Clients \ Range(sched)

\* Resources that may be held or requested "ahead" of the i-th scheduled client
PrevResources(i) ==
       available
  \cup (UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) })
  \cup (UNION { alloc[c] : c \in UnscheduledClients })

AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) : sched[i] # sched[j]
  /\ \A c \in UnscheduledClients : unsat[c] # {} => alloc[c] = {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) :
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------

THEOREM Allocator => []TypeInvariant
THEOREM Allocator => []ResourceMutex
THEOREM Allocator => []AllocatorInvariant
THEOREM Allocator => ClientsWillReturn
THEOREM Allocator => ClientsWillObtain
THEOREM Allocator => InfOftenSatisfied

=========================================================================