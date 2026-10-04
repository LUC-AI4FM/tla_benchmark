---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    sched       \* sequence of clients whose requests may be served (schedule)

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Type definitions *)

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

-----------------------------------------------------------------------------
(* Helper operators *)

\* Set of resources currently available (not allocated to anyone)
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of all resources currently requested by any client
requested == UNION {unsat[c] : c \in Clients}

\* A client is eligible to make a request if it has no outstanding request and holds no resources
canRequest(c) == unsat[c] = {} /\ alloc[c] = {}

\* A client is fully satisfied when it has received all requested resources
satisfied(c) == unsat[c] = {} /\ alloc[c] /= {}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

\* Client c requests a non-empty set S of resources
Request(c, S) ==
    /\ canRequest(c)
    /\ S /= {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = Append(sched, c)

\* Allocate a non-empty subset S of available resources to client c
\* The client must be at the head of the schedule and requesting those resources
Allocate(c, S) ==
    /\ sched /= <<>>
    /\ Head(sched) = c
    /\ S /= {}
    /\ S \subseteq unsat[c]
    /\ S \subseteq available
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ IF unsat'[c] = {}
       THEN sched' = Tail(sched)
       ELSE sched' = sched

\* Client c returns a non-empty subset S of its allocated resources
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

\* Schedule action: move a client from later in the schedule to the front
\* This represents rescheduling to allow fairness in serving requests
Schedule ==
    /\ Len(sched) > 1
    /\ \E i \in 2..Len(sched):
        sched' = <<sched[i]>> \o SubSeq(sched, 1, i-1) \o SubSeq(sched, i+1, Len(sched))
    /\ unsat' = unsat
    /\ alloc' = alloc

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)
    \/ Schedule

-----------------------------------------------------------------------------
(* Fairness conditions *)

\* Clients eventually return resources once fully satisfied
ReturnFairness == \A c \in Clients : WF_vars(\E S \in SUBSET alloc[c] : S /= {} /\ Return(c, S))

\* Allocations eventually happen when enabled
AllocationFairness == \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))

\* Scheduling eventually occurs when enabled
ScheduleFairness == WF_vars(Schedule)

Fairness == ReturnFairness /\ AllocationFairness /\ ScheduleFairness

-----------------------------------------------------------------------------
(* Complete specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

\* Mutual exclusion: no resource is allocated to more than one client
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

\* Allocator invariant: allocated resources are a subset of all resources
AllocatorInvariant ==
    /\ \A c \in Clients : alloc[c] \subseteq Resources
    /\ \A c \in Clients : unsat[c] \subseteq Resources
    /\ (UNION {alloc[c] : c \in Clients}) \subseteq Resources

\* All invariants combined
Invariants == TypeInvariant /\ MutualExclusion /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Eventually, any client holding resources will return them all
EventualReturn ==
    \A c \in Clients : alloc[c] /= {} ~> alloc[c] = {}

\* Eventually, any unsatisfied request will be satisfied
EventualObtainment ==
    \A c \in Clients : unsat[c] /= {} ~> unsat[c] = {}

\* Infinitely often, some client becomes satisfied (gets all requested resources)
InfinitelyOftenSatisfied ==
    []<>(\E c \in Clients : satisfied(c))

\* Combined liveness properties
LivenessProperties == EventualReturn /\ EventualObtainment

=============================================================================