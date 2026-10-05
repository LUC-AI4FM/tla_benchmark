---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Sequences, FiniteSets, Naturals, TLC

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

vars == <<unsat, alloc, sched>>

TypeOK ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

--------------------------------------------------------------------------------
(* Helper definitions *)

\* Set of all resources currently available (not allocated to any client)
Available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of clients that appear in the schedule
Scheduled == {sched[i] : i \in 1..Len(sched)}

\* Set of clients with pending requests that are not yet scheduled
Unscheduled == {c \in Clients : unsat[c] /= {} /\ c \notin Scheduled}

\* Resources requested by clients appearing before position i in schedule
PriorRequests(i) ==
    UNION {unsat[sched[j]] : j \in 1..(i-1)}

\* Position of client c in schedule (0 if not scheduled)
Position(c) ==
    IF c \notin Scheduled THEN 0
    ELSE CHOOSE i \in 1..Len(sched) : sched[i] = c

\* Remove client at position i from schedule
RemoveFromSchedule(i) ==
    [j \in 1..(Len(sched)-1) |-> IF j < i THEN sched[j] ELSE sched[j+1]]

\* All permutations of a set as sequences
PermSeqs(S) ==
    {seq \in [1..Cardinality(S) -> S] : 
        \A i, j \in 1..Cardinality(S) : i /= j => seq[i] /= seq[j]}

--------------------------------------------------------------------------------
(* Actions *)

\* A client with no pending requests and no held resources submits a new request
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S /= {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED <<alloc, sched>>

\* Append a permutation of unscheduled clients with pending requests to schedule
Schedule ==
    /\ Unscheduled /= {}
    /\ \E perm \in PermSeqs(Unscheduled) :
        sched' = sched \o perm
    /\ UNCHANGED <<unsat, alloc>>

\* Allocate resources to a scheduled client
Allocate(c, S) ==
    /\ c \in Scheduled
    /\ S /= {}
    /\ S \subseteq Available
    /\ S \subseteq unsat[c]
    /\ LET pos == Position(c)
       IN PriorRequests(pos) \cap S = {}
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ IF unsat[c] \ S = {}
       THEN sched' = RemoveFromSchedule(Position(c))
       ELSE UNCHANGED sched

\* A client returns a subset of its held resources
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED <<unsat, sched>>

--------------------------------------------------------------------------------
(* Specification *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ Schedule
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)

--------------------------------------------------------------------------------
(* Fairness conditions *)

\* Full return when request is satisfied
FullReturn(c) ==
    /\ unsat[c] = {}
    /\ alloc[c] /= {}
    /\ Return(c, alloc[c])

\* Any partial allocation for a client
AnyAllocation(c) ==
    \E S \in SUBSET Resources : Allocate(c, S)

Fairness ==
    /\ \A c \in Clients : WF_vars(FullReturn(c))
    /\ \A c \in Clients : WF_vars(AnyAllocation(c))
    /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Safety Invariants *)

\* Mutual exclusion: no resource is allocated to multiple clients
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

\* Structural allocator invariant ensuring schedulability
AllocatorInvariant ==
    /\ \A c \in Clients : alloc[c] \cap unsat[c] = {}
    /\ \A i \in 1..Len(sched) : sched[i] \in Clients
    /\ \A i, j \in 1..Len(sched) : i /= j => sched[i] /= sched[j]
    /\ \A c \in Scheduled : unsat[c] /= {}
    /\ \A c \in Clients : unsat[c] \subseteq Resources
    /\ \A c \in Clients : alloc[c] \subseteq Resources

Safety == TypeOK /\ MutualExclusion /\ AllocatorInvariant

--------------------------------------------------------------------------------
(* Liveness Properties *)

\* Clients eventually return all resources
ClientsEventuallyReturn ==
    \A c \in Clients : [](alloc[c] /= {} => <>(alloc[c] = {}))

\* Every requested resource is eventually allocated
ResourcesEventuallyAllocated ==
    \A c \in Clients : \A r \in Resources : 
        [](r \in unsat[c] => <>(r \in alloc[c]))

\* Every client is infinitely often fully satisfied
ClientsInfinitelyOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {} /\ alloc[c] = {})

Liveness ==
    /\ ClientsEventuallyReturn
    /\ ResourcesEventuallyAllocated
    /\ ClientsInfinitelyOftenSatisfied

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrectness == Spec => []TypeOK

THEOREM MutualExclusionTheorem == Spec => []MutualExclusion

THEOREM AllocatorInvariantTheorem == Spec => []AllocatorInvariant

THEOREM EventualReturnTheorem == Spec => ClientsEventuallyReturn

THEOREM EventualAllocationTheorem == Spec => ResourcesEventuallyAllocated

THEOREM InfinitelyOftenSatisfiedTheorem == Spec => ClientsInfinitelyOftenSatisfied

================================================================================