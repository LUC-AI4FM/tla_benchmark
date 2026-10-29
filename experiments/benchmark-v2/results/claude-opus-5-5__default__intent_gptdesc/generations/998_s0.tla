------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,   \* unsat[c]: resources requested by client c and not yet allocated
  alloc,   \* alloc[c]: resources currently held by client c
  sched    \* schedule: sequence of clients with outstanding requests

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Resources not held by any client
available == Resources \ (UNION { alloc[c] : c \in Clients })

\* Remove the i-th element of a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* The set of all permutations of the elements of a finite set S
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { <<>> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Clients with outstanding requests that are not yet in the schedule
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

UnscheduledClients == Clients \ Range(sched)

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

\* A client may issue a new request only when its previous request has been
\* fully satisfied and it holds no resources.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

\* Allocate a (possibly partial) set S of available, requested resources to a
\* scheduled client c, provided no earlier client in the schedule still
\* requests any resource in S. Fully satisfied clients leave the schedule.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* A client returns a (possibly partial) set of the resources it holds.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

\* Extend the schedule with all currently requesting, unscheduled clients
\* in an arbitrary order.
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

-----------------------------------------------------------------------------
(* Fairness *)

\* Clients eventually return all held resources once fully satisfied.
ClientsFairness ==
  \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))

\* The allocator eventually performs possible allocations and schedules.
AllocatorFairness ==
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ ClientsFairness /\ AllocatorFairness

-----------------------------------------------------------------------------
(* Safety properties *)

Mutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

\* Every scheduled client has an outstanding request; no duplicates.
ScheduledAreRequesting ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i, j \in DOMAIN sched : i # j => sched[i] # sched[j]

\* A client never holds a resource requested by an earlier scheduled client.
NoHoldOfEarlierRequests ==
  \A i \in DOMAIN sched : \A j \in 1..(i-1) :
     alloc[sched[i]] \cap unsat[sched[j]] = {}

\* Unscheduled clients hold nothing requested by scheduled clients.
UnscheduledNoConflict ==
  \A c \in UnscheduledClients : \A s \in Range(sched) :
     alloc[c] \cap unsat[s] = {}

\* Resources that will become available to sched[i] once earlier clients release
PrevResources(i) ==
  alloc[sched[i]]
  \cup UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) }
  \cup UNION { alloc[c] : c \in UnscheduledClients }

\* Allocation feasibility
Feasibility ==
  \A i \in DOMAIN sched :
     unsat[sched[i]] \subseteq available \cup PrevResources(i)

AllocatorInvariant ==
  /\ ScheduledAreRequesting
  /\ NoHoldOfEarlierRequests
  /\ UnscheduledNoConflict
  /\ Feasibility

Safety == TypeInvariant /\ Mutex /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

EventuallyScheduled ==
  \A c \in Clients : (unsat[c] # {}) ~> (c \in Range(sched) \/ unsat[c] = {})

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

Liveness ==
  /\ ClientsWillReturn
  /\ ClientsWillObtain
  /\ EventuallyScheduled
  /\ InfOftenSatisfied

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================