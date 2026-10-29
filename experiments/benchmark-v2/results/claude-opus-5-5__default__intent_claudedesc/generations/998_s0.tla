------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,      \* set of clients
  Resources     \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,   \* unsat[c]: resources requested by c that are not yet allocated
  alloc,   \* alloc[c]: resources currently held by c
  sched    \* sequence of clients with pending requests, in schedule order

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Resources that no client currently holds
available == Resources \ (UNION { alloc[c] : c \in Clients })

\* Clients with pending requests that are not yet scheduled
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

\* The set of all permutations of the elements of a finite set S, as sequences
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the i-th element of a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

\* Client c requests a non-empty set S of resources. It may do so only if
\* all its prior requests have been satisfied and it holds no resources.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

\* Allocate a non-empty set S of available resources to scheduled client c,
\* provided no client earlier in the schedule has requested any of them.
\* If the request becomes fully satisfied, c is removed from the schedule.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* Client c returns a non-empty set S of resources it holds.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

\* Extend the schedule by a permutation of the unscheduled pending clients.
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

\* Fairness assumptions:
\*  - clients eventually return all held resources once fully satisfied
\*  - the allocator eventually allocates available resources to scheduled clients
\*  - the allocator eventually schedules pending clients
Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No resource is held by two different clients
Mutex ==
  \A c1, c2 \in Clients : alloc[c1] \cap alloc[c2] # {} => c1 = c2

UnscheduledClients == Clients \ Range(sched)

\* Resources that may be held by the time scheduled client sched[i] needs them:
\* its own allocation, everything requested or held by earlier-scheduled
\* clients, and everything held by unscheduled clients.
PrevResources(i) ==
       alloc[sched[i]]
  \cup UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) }
  \cup UNION { alloc[c] : c \in UnscheduledClients }

AllocatorInvariant ==
  \* every scheduled client has an outstanding request
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  \* the schedule contains no duplicates
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) : sched[i] # sched[j]
  \* unscheduled clients with pending requests hold no resources
  /\ \A c \in toSchedule : alloc[c] = {}
  \* each scheduled client's request can be satisfied, assuming that
  \* earlier-scheduled clients eventually release their resources
  /\ \A i \in DOMAIN sched :
        \A r \in unsat[sched[i]] : r \in available \/ r \in PrevResources(i)

Safety == TypeInvariant /\ Mutex /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every client eventually obtains each resource it requests
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

\* Every fully satisfied client eventually releases all its resources
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

\* Every client is fully satisfied infinitely often
InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Mutex /\ AllocatorInvariant)
THEOREM Spec => ClientsWillObtain /\ ClientsWillReturn /\ InfOftenSatisfied
=============================================================================