---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Sequences, FiniteSets, Naturals, TLC

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Type definitions and helper operators *)

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

(* Available resources: those not allocated to any client *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(* Set of clients that appear in the schedule *)
scheduled == {sched[i] : i \in 1..Len(sched)}

(* Clients with pending requests that are not yet scheduled *)
unscheduled == {c \in Clients : unsat[c] # {} /\ c \notin scheduled}

(* Position of client c in schedule, or 0 if not scheduled *)
PositionInSchedule(c) ==
    IF c \notin scheduled THEN 0
    ELSE CHOOSE i \in 1..Len(sched) : sched[i] = c

(* Resources requested by clients appearing before position p in schedule *)
RequestedByEarlier(p) ==
    UNION {unsat[sched[i]] : i \in 1..(p-1)}

(* Remove client c from the schedule *)
RemoveFromSchedule(c) ==
    SelectSeq(sched, LAMBDA x: x # c)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Request: a client with no pending requests and no held resources submits a new non-empty request *)
Request(c, S) ==
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ S # {}
    /\ S \subseteq Resources
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED <<alloc, sched>>

(* Schedule: append a permutation of all unscheduled clients with pending requests *)
Schedule ==
    /\ unscheduled # {}
    /\ \E perm \in {f \in [1..Cardinality(unscheduled) -> unscheduled] :
                    \A x, y \in 1..Cardinality(unscheduled) : x # y => f[x] # f[y]} :
        LET newSeq == [i \in 1..Cardinality(unscheduled) |-> perm[i]]
        IN sched' = sched \o newSeq
    /\ UNCHANGED <<unsat, alloc>>

(* Allocate: grant resources to a scheduled client if no earlier client wants them *)
Allocate(c, S) ==
    /\ c \in scheduled
    /\ S # {}
    /\ S \subseteq available
    /\ S \subseteq unsat[c]
    /\ LET pos == PositionInSchedule(c)
       IN S \cap RequestedByEarlier(pos) = {}
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ IF unsat'[c] = {}
       THEN sched' = RemoveFromSchedule(c)
       ELSE UNCHANGED sched

(* Return: a client releases any subset of its held resources *)
Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED <<unsat, sched>>

-----------------------------------------------------------------------------
(* Next-state relation *)

Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ Schedule
    \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c, S)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)

-----------------------------------------------------------------------------
(* Fairness conditions *)

(* Full return when request is satisfied *)
FullReturn(c) == unsat[c] = {} /\ alloc[c] # {} /\ Return(c, alloc[c])

(* Any allocation for client c *)
AnyAllocation(c) == \E S \in SUBSET Resources : S # {} /\ Allocate(c, S)

Fairness ==
    /\ \A c \in Clients : WF_vars(FullReturn(c))
    /\ \A c \in Clients : WF_vars(AnyAllocation(c))
    /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

(* Mutual exclusion: no resource is allocated to more than one client *)
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Allocator invariant ensuring schedulability *)
AllocatorInvariant ==
    /\ \A c \in Clients : alloc[c] \subseteq Resources
    /\ \A c \in Clients : unsat[c] \subseteq Resources
    /\ \A c \in Clients : alloc[c] \cap unsat[c] = {}
    /\ \A i \in 1..Len(sched) : sched[i] \in Clients
    /\ \A i, j \in 1..Len(sched) : i # j => sched[i] # sched[j]
    /\ \A c \in scheduled : unsat[c] # {}

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Clients eventually return all resources *)
ClientsEventuallyReturn ==
    \A c \in Clients : (alloc[c] # {} ~> alloc[c] = {})

(* Every requested resource is eventually allocated *)
RequestsEventuallyAllocated ==
    \A c \in Clients : \A r \in Resources : (r \in unsat[c] ~> r \in alloc[c])

(* Every client is infinitely often fully satisfied (no pending requests and no allocations) *)
ClientsInfinitelyOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {} /\ alloc[c] = {})

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrectness == Spec => []TypeInvariant

THEOREM MutualExclusionTheorem == Spec => []MutualExclusion

THEOREM AllocatorInvariantTheorem == Spec => []AllocatorInvariant

THEOREM LivenessReturn == Spec => ClientsEventuallyReturn

THEOREM LivenessAllocation == Spec => RequestsEventuallyAllocated

THEOREM LivenessSatisfaction == Spec => ClientsInfinitelyOftenSatisfied

=============================================================================