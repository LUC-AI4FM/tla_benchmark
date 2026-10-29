------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

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

-------------------------------------------------------------------------
\* Auxiliary definitions

\* The set of resources that are currently not allocated to any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* The range of a function / sequence
Range(f) == { f[x] : x \in DOMAIN f }

\* The set of permutations of a finite set, represented as sequences
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the element at position i from a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* Clients with pending requests that have not yet been scheduled
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

-------------------------------------------------------------------------
\* Initial state and actions

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

\* A client c may request a set of resources only if it has no outstanding
\* unsatisfied request and currently holds no resources.
Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

\* Allocation of a set of available resources to a scheduled client.
\* The request may be partially satisfied. Resources may only be given to
\* client c if no client scheduled before c is still waiting for them.
Allocate(c, S) ==
  /\ S # {} /\ S \subseteq (available \cap unsat[c])
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* Client c returns a set of resources it holds (possibly early).
Return(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

\* The allocator extends its schedule by the clients with pending,
\* unscheduled requests, in some arbitrary order.
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

-------------------------------------------------------------------------
\* Fairness assumptions

Liveness ==
  \* clients return resources once their requests are fully satisfied
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  \* allocations eventually happen when enabled
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  \* scheduling eventually occurs
  /\ WF_vars(Schedule)

Allocator ==
  /\ Init
  /\ [][Next]_vars
  /\ Liveness

Spec == Allocator

-------------------------------------------------------------------------
\* Safety properties

ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients == Clients \ Range(sched)

\* Resources that may be held by clients preceding position i in the
\* schedule, by the client at position i, or by unscheduled clients
PrevResources(i) ==
  alloc[sched[i]]
  \cup (UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) })
  \cup (UNION { alloc[c] : c \in UnscheduledClients })

AllocatorInvariant ==
  \* every client appears at most once in the schedule
  /\ \A i, j \in DOMAIN sched : i # j => sched[i] # sched[j]
  \* every scheduled client has a pending request
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  \* outstanding and allocated resources of a client are disjoint
  /\ \A c \in Clients : unsat[c] \cap alloc[c] = {}
  \* clients waiting to be scheduled hold no resources
  /\ \A c \in toSchedule : alloc[c] = {}
  \* a scheduled client does not hold resources needed by earlier clients
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) :
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  \* resources needed by scheduled clients are available or held by
  \* clients that are entitled to them
  /\ \A i \in DOMAIN sched :
        unsat[sched[i]] \subseteq (available \cup PrevResources(i))

-------------------------------------------------------------------------
\* Liveness properties

\* Clients whose requests have been satisfied will eventually return them
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {} ~> alloc[c] = {})

\* Every requested resource is eventually obtained
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c] ~> r \in alloc[c])

\* Every client's requests are satisfied infinitely often
InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------
THEOREM Allocator => []TypeInvariant
THEOREM Allocator => []ResourceMutex
THEOREM Allocator => []AllocatorInvariant
THEOREM Allocator => ClientsWillReturn
THEOREM Allocator => ClientsWillObtain
THEOREM Allocator => InfOftenSatisfied
=============================================================================