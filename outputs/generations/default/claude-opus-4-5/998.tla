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

(* A client can only request resources if it has no outstanding request and holds nothing *)
ClientCanRequest(c) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}

(* Available resources: not allocated to any client *)
Available == Resources \ (UNION {alloc[c] : c \in Clients})

(* Mutual exclusion: no resource allocated to more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Allocator invariant: unsatisfied requests don't overlap with allocations *)
AllocatorInvariant ==
    \A c \in Clients : unsat[c] \cap alloc[c] = {}

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeInvariant
    /\ MutualExclusion
    /\ AllocatorInvariant

-----------------------------------------------------------------------------
(* Helper: check if client c appears in schedule *)
InSchedule(c) == \E i \in 1..Len(sched) : sched[i] = c

(* Helper: remove first occurrence of c from schedule *)
RemoveFromSchedule(c) ==
    IF ~InSchedule(c) THEN sched
    ELSE LET i == CHOOSE j \in 1..Len(sched) : 
                    /\ sched[j] = c 
                    /\ \A k \in 1..(j-1) : sched[k] # c
         IN SubSeq(sched, 1, i-1) \o SubSeq(sched, i+1, Len(sched))

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Client c requests a non-empty set of resources S *)
Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ ClientCanRequest(c)
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ alloc' = alloc
    /\ sched' = Append(sched, c)

(* Allocate a subset of available resources to client c *)
(* Only clients at the head of schedule can receive allocations *)
Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq Available
    /\ S \subseteq unsat[c]
    /\ Len(sched) > 0
    /\ sched[1] = c
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ sched' = IF unsat'[c] = {} THEN RemoveFromSchedule(c) ELSE sched

(* Client c returns a subset of its allocated resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ unsat' = unsat
    /\ sched' = sched

(* Scheduling action: reorder the schedule (allow any permutation that maintains the set) *)
Schedule ==
    /\ Len(sched) > 1
    /\ \E newSched \in Seq(Clients) :
        /\ Len(newSched) = Len(sched)
        /\ \A c \in Clients : 
            Cardinality({i \in 1..Len(sched) : sched[i] = c}) = 
            Cardinality({i \in 1..Len(newSched) : newSched[i] = c})
        /\ newSched # sched
        /\ sched' = newSched
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

(* Client returns all resources once fully satisfied (unsat = {} and alloc # {}) *)
ClientReturns(c) ==
    /\ unsat[c] = {}
    /\ alloc[c] # {}
    /\ Return(c, alloc[c])

(* Allocation is possible for some client *)
AllocationEnabled ==
    \E c \in Clients, S \in SUBSET Resources :
        /\ S # {}
        /\ S \subseteq Available
        /\ S \subseteq unsat[c]
        /\ Len(sched) > 0
        /\ sched[1] = c

AllocateAction ==
    \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)

(* Fairness: clients return resources once satisfied, allocations happen, scheduling occurs *)
Fairness ==
    /\ \A c \in Clients : WF_vars(ClientReturns(c))
    /\ WF_vars(AllocateAction)
    /\ WF_vars(Schedule)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Eventual return: if a client holds resources with no outstanding request, it eventually returns them *)
EventualReturn ==
    \A c \in Clients : (unsat[c] = {} /\ alloc[c] # {}) ~> (alloc[c] = {})

(* Eventual obtainment: if a client requests resources, it eventually gets all of them *)
EventualObtainment ==
    \A c \in Clients : (unsat[c] # {}) ~> (unsat[c] = {})

(* Infinitely often satisfied: clients are satisfied infinitely often *)
(* Expressed as: it's always eventually true that some client transitions to satisfied *)
ClientSatisfied(c) == unsat[c] = {} /\ alloc[c] # {}

InfinitelyOftenSatisfied ==
    \A c \in Clients : []<>(ClientSatisfied(c) \/ (unsat[c] = {} /\ alloc[c] = {}))

(* Combined liveness *)
Liveness ==
    /\ EventualReturn
    /\ EventualObtainment

=============================================================================