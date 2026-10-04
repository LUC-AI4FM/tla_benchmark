---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    sched       \* sequence of clients whose requests may be served (in order)

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Type definitions and invariants *)

TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

(* All resources currently allocated *)
AllocatedResources == UNION {alloc[c] : c \in Clients}

(* Available resources *)
Available == Resources \ AllocatedResources

(* Mutual exclusion: no resource is allocated to more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Allocator invariant: unsatisfied requests and allocations are disjoint for each client *)
AllocatorInvariant ==
    \A c \in Clients : unsat[c] \cap alloc[c] = {}

(* Each client appears at most once in the schedule *)
ScheduleInvariant ==
    \A i, j \in 1..Len(sched) : i # j => sched[i] # sched[j]

(* Combined safety invariant *)
Safety == TypeOK /\ MutualExclusion /\ AllocatorInvariant /\ ScheduleInvariant

-----------------------------------------------------------------------------
(* Helper: Remove client c from schedule *)
RemoveFromSchedule(c) ==
    SelectSeq(sched, LAMBDA x : x # c)

(* Helper: Client c is in the schedule *)
InSchedule(c) ==
    \E i \in 1..Len(sched) : sched[i] = c

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Client c requests a non-empty set S of resources.
   Precondition: c has no outstanding request and holds no resources *)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = sched

(* Schedule client c: add c to end of schedule if c has unsatisfied requests
   and is not already scheduled *)
Schedule(c) ==
    /\ unsat[c] # {}
    /\ ~InSchedule(c)
    /\ sched' = Append(sched, c)
    /\ unsat' = unsat
    /\ alloc' = alloc

(* Allocate a non-empty subset S of available resources to client c.
   c must be first in schedule, and S must be subset of what c still needs *)
Allocate(c, S) ==
    /\ S # {}
    /\ Len(sched) > 0
    /\ sched[1] = c
    /\ S \subseteq unsat[c]
    /\ S \subseteq Available
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ sched' = IF unsat[c] \ S = {} 
                THEN RemoveFromSchedule(c)
                ELSE sched

(* Client c returns a non-empty subset S of its allocated resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients : Schedule(c)
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Fairness conditions *)

(* Client c is fully satisfied (got everything requested, nothing outstanding) *)
Satisfied(c) == unsat[c] = {} /\ alloc[c] # {}

(* Weak fairness: clients return resources once fully satisfied *)
ClientReturnFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET alloc[c] : S # {} /\ Return(c, S))

(* Weak fairness: allocations eventually happen when enabled *)
AllocationFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET Resources : S # {} /\ Allocate(c, S))

(* Weak fairness: scheduling eventually occurs *)
SchedulingFairness ==
    \A c \in Clients : WF_vars(Schedule(c))

Fairness == ClientReturnFairness /\ AllocationFairness /\ SchedulingFairness

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Liveness properties *)

(* If a client holds resources and has no outstanding requests, 
   it eventually returns all resources *)
EventualReturn ==
    \A c \in Clients : Satisfied(c) ~> alloc[c] = {}

(* If a client requests resources, it eventually obtains all of them *)
EventualObtainment ==
    \A c \in Clients : unsat[c] # {} ~> (unsat[c] = {} /\ alloc[c] # {})

(* Requests are infinitely often satisfied: if a client makes a request,
   it will eventually be fully satisfied *)
InfinitelyOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
(* Properties to check *)

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => []ScheduleInvariant
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => InfinitelyOftenSatisfied

=============================================================================