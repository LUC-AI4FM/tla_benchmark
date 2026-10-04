---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Clients,        \* The set of clients
    Resources       \* The set of resources

VARIABLES
    requests,       \* requests[c] = set of resources requested by client c
    alloc,          \* alloc[c] = set of resources currently allocated to client c
    available,      \* set of resources currently available for allocation
    schedule        \* sequence of clients whose requests may be served

-----------------------------------------------------------------------------
(* Type definitions and type invariant *)

TypeOK ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ available \subseteq Resources
    /\ schedule \in Seq(Clients)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ available = Resources
    /\ schedule = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Client c issues a request for a non-empty set S of resources.
   Clients can only request when they have no outstanding request and hold no resources. *)
Request(c, S) ==
    /\ requests[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ requests' = [requests EXCEPT ![c] = S]
    /\ UNCHANGED <<alloc, available, schedule>>

(* Allocate a non-empty subset S of available resources to client c.
   The client must be scheduled (at head of schedule or in schedule)
   and S must be a subset of both requested and available resources. *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq requests[c]
    /\ \E i \in 1..Len(schedule) : schedule[i] = c
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ available' = available \ S
    /\ requests' = [requests EXCEPT ![c] = @ \ S]
    /\ UNCHANGED schedule

(* Client c returns a non-empty subset S of its currently held resources. *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ available' = available \cup S
    /\ UNCHANGED <<requests, schedule>>

(* Schedule a client c that has a pending request and is not yet scheduled.
   Add the client to the end of the schedule. *)
Schedule(c) ==
    /\ requests[c] # {}
    /\ \A i \in 1..Len(schedule) : schedule[i] # c
    /\ schedule' = Append(schedule, c)
    /\ UNCHANGED <<requests, alloc, available>>

(* Remove a client from the schedule when its request is fully satisfied
   (requests[c] = {}) or when it's no longer relevant *)
Unschedule(c) ==
    /\ \E i \in 1..Len(schedule) : schedule[i] = c
    /\ requests[c] = {}
    /\ schedule' = SelectSeq(schedule, LAMBDA x : x # c)
    /\ UNCHANGED <<requests, alloc, available>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)
    \/ \E c \in Clients : Schedule(c)
    \/ \E c \in Clients : Unschedule(c)

-----------------------------------------------------------------------------
(* Helper definitions for fairness *)

ReturnAll(c) ==
    /\ alloc[c] # {}
    /\ alloc' = [alloc EXCEPT ![c] = {}]
    /\ available' = available \cup alloc[c]
    /\ UNCHANGED <<requests, schedule>>

(* A client is fully satisfied when it has no outstanding requests
   and holds some resources *)
FullySatisfied(c) == requests[c] = {} /\ alloc[c] # {}

(* Allocation is enabled for client c *)
AllocationEnabled(c) ==
    /\ \E i \in 1..Len(schedule) : schedule[i] = c
    /\ \E S \in SUBSET (available \cap requests[c]) : S # {}

(* Scheduling is enabled for client c *)
SchedulingEnabled(c) ==
    /\ requests[c] # {}
    /\ \A i \in 1..Len(schedule) : schedule[i] # c

-----------------------------------------------------------------------------
(* Fairness conditions *)

(* Weak fairness: clients eventually return resources once fully satisfied *)
ClientFairness ==
    \A c \in Clients : WF_<<requests, alloc, available, schedule>>(ReturnAll(c))

(* Weak fairness: allocations eventually happen when enabled *)
AllocationFairness ==
    \A c \in Clients, S \in SUBSET Resources :
        WF_<<requests, alloc, available, schedule>>(Allocate(c, S))

(* Weak fairness: scheduling eventually occurs when enabled *)
SchedulingFairness ==
    \A c \in Clients : WF_<<requests, alloc, available, schedule>>(Schedule(c))

(* Weak fairness for unscheduling *)
UnscheduleFairness ==
    \A c \in Clients : WF_<<requests, alloc, available, schedule>>(Unschedule(c))

Fairness ==
    /\ ClientFairness
    /\ AllocationFairness
    /\ SchedulingFairness
    /\ UnscheduleFairness

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_<<requests, alloc, available, schedule>> /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Mutual exclusion: no resource is allocated to more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* All allocated resources and available resources partition the resource set *)
ResourcePartition ==
    available \cup UNION {alloc[c] : c \in Clients} = Resources

(* No resource is both available and allocated *)
NoDoubleAllocation ==
    \A c \in Clients : available \cap alloc[c] = {}

(* Allocator invariant: combines resource conservation properties *)
AllocatorInvariant ==
    /\ ResourcePartition
    /\ NoDoubleAllocation
    /\ MutualExclusion

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Eventual return: if a client holds resources and has no pending requests,
   it will eventually return all resources *)
EventualReturn ==
    \A c \in Clients : FullySatisfied(c) ~> alloc[c] = {}

(* Eventual obtainment: if a client requests resources, it will eventually
   obtain all requested resources (requests become empty through allocation) *)
EventualObtainment ==
    \A c \in Clients : requests[c] # {} ~> requests[c] = {}

(* Infinitely often satisfied: if clients keep making requests,
   requests are infinitely often satisfied *)
InfinitelyOftenSatisfied ==
    []<>(\E c \in Clients : alloc[c] # {} /\ requests[c] = {})

(* Every request is eventually scheduled *)
EventuallyScheduled ==
    \A c \in Clients : requests[c] # {} ~> \E i \in 1..Len(schedule) : schedule[i] = c

(* Liveness: combination of all liveness properties *)
Liveness ==
    /\ EventualReturn
    /\ EventualObtainment

=============================================================================