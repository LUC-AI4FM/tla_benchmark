---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES
    unsat,      \* unsat[c] = set of resources client c has requested but not yet received
    alloc,      \* alloc[c] = set of resources currently allocated to client c
    sched       \* sequence of clients whose requests may be served (scheduling order)

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Type definitions and invariants *)

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

(* Mutual exclusion: no resource is allocated to more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Available resources: those not allocated to any client *)
available == Resources \ UNION {alloc[c] : c \in Clients}

(* Allocator invariant: unsatisfied requests don't overlap with allocations *)
AllocatorInvariant ==
    \A c \in Clients : unsat[c] \cap alloc[c] = {}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Client c requests a non-empty set S of resources.
   Allowed only when c has no outstanding request and holds no resources. *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = Append(sched, c)

(* Allocate a non-empty subset S of requested resources to client c.
   c must be at the head of the schedule, and S must be available and requested. *)
Allocate(c, S) ==
    /\ sched # <<>>
    /\ Head(sched) = c
    /\ S # {}
    /\ S \subseteq unsat[c] \cap available
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ sched' = sched

(* Client c returns a non-empty subset S of its allocated resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

(* Remove client from head of schedule when its request is fully satisfied *)
Schedule ==
    /\ sched # <<>>
    /\ unsat[Head(sched)] = {}
    /\ sched' = Tail(sched)
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

(* A client is satisfied when it has no outstanding requests but holds resources *)
Satisfied(c) == unsat[c] = {} /\ alloc[c] # {}

(* Weak fairness for returning resources once fully satisfied *)
ReturnFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET alloc[c] : S # {} /\ Return(c, S))

(* Weak fairness for allocation *)
AllocationFairness ==
    \A c \in Clients : WF_vars(\E S \in SUBSET (unsat[c] \cap available) : S # {} /\ Allocate(c, S))

(* Weak fairness for scheduling *)
ScheduleFairness == WF_vars(Schedule)

Fairness == ReturnFairness /\ AllocationFairness /\ ScheduleFairness

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Liveness properties *)

(* If a client holds resources, it eventually returns all of them *)
EventualReturn ==
    \A c \in Clients : alloc[c] # {} ~> alloc[c] = {}

(* If a client requests resources, it eventually obtains them all *)
EventualObtainment ==
    \A c \in Clients : unsat[c] # {} ~> (unsat[c] = {} /\ alloc[c] # {})

(* Infinitely often some client request is satisfied *)
InfinitelyOftenSatisfied ==
    []<>(\E c \in Clients : Satisfied(c))

(* Combined liveness properties *)
LivenessProperties ==
    /\ EventualReturn
    /\ EventualObtainment
    /\ InfinitelyOftenSatisfied

-----------------------------------------------------------------------------
(* Theorems to check *)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusion
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => LivenessProperties

=============================================================================