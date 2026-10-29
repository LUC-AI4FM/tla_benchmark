------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,   \* unsat[c] denotes the outstanding requests of client c
  alloc,   \* alloc[c] denotes the resources allocated to client c
  pool,    \* set of clients that have requests but are not yet scheduled
  sched    \* schedule represented as a sequence of clients

vars == <<unsat, alloc, pool, sched>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Resources that are not currently allocated to any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of all sequences that enumerate the elements of S exactly once
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] }]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the i-th element from a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ pool \in SUBSET Clients
  /\ sched \in Seq(Clients)

-----------------------------------------------------------------------------
Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ pool  = {}
  /\ sched = << >>

\* A client c may request a set S of resources provided that it has
\* no outstanding unsatisfied request and holds no resources.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ pool'  = pool \cup {c}
  /\ UNCHANGED <<alloc, sched>>

\* Allocation of a set S of available resources to a client that has
\* requested them; the client must appear in the schedule and no
\* client that precedes it in the schedule may be waiting for any of
\* the resources in S. Requests may be satisfied partially.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<pool>>

\* Client c returns a set S of resources it holds (possibly early).
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, pool, sched>>

\* The allocator extends its schedule by the clients in the pool,
\* in some arbitrary order.
Schedule ==
  /\ pool # {}
  /\ \E sq \in PermSeqs(pool) : sched' = sched \o sq
  /\ pool' = {}
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

-----------------------------------------------------------------------------
(* Fairness assumptions:
   - clients return resources once their requests are fully satisfied,
   - the allocator eventually allocates resources when possible,
   - the allocator eventually schedules waiting clients. *)
Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

SchedulingAllocator == Init /\ [][Next]_vars /\ Liveness

Spec == SchedulingAllocator

-----------------------------------------------------------------------------
(* Safety properties *)

ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

\* Clients that do not appear in the schedule
UnscheduledClients == Clients \ Range(sched)

\* Resources that will be available when the i-th scheduled client
\* has to be satisfied
PrevResources(i) ==
  available
  \cup (UNION {unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1)})
  \cup (UNION {alloc[c] : c \in UnscheduledClients})

AllocatorInvariant ==
  /\ \A c \in pool : unsat[c] # {} /\ alloc[c] = {}
  /\ \A i \in DOMAIN sched :
        /\ unsat[sched[i]] # {}
        /\ \A j \in 1..(i-1) : alloc[sched[i]] \cap unsat[sched[j]] = {}
        /\ unsat[sched[i]] \subseteq PrevResources(i)
  /\ \A i, j \in DOMAIN sched : i # j => sched[i] # sched[j]
  /\ pool \cap Range(sched) = {}

-----------------------------------------------------------------------------
(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {} ~> alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
THEOREM SchedulingAllocator => []TypeInvariant
THEOREM SchedulingAllocator => []ResourceMutex
THEOREM SchedulingAllocator => []AllocatorInvariant
THEOREM SchedulingAllocator => ClientsWillReturn
THEOREM SchedulingAllocator => ClientsWillObtain
THEOREM SchedulingAllocator => InfOftenSatisfied

=============================================================================