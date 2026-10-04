---------------------------- MODULE ResourceAllocator ----------------------------

CONSTANTS
    Clients,
    Resources

VARIABLES
    unsat,
    alloc,
    sched

vars == <<unsat, alloc, sched>>

----------------------------------------------------------------------------

(* Type invariant and auxiliary definitions *)

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    /\ sched \in Seq(Clients)

(* Set of all resources currently allocated to some client *)
AllocatedResources == UNION {alloc[c] : c \in Clients}

(* Available resources: those not allocated to any client *)
AvailableResources == Resources \ AllocatedResources

(* Clients that appear in the schedule *)
ScheduledClients == {sched[i] : i \in 1..Len(sched)}

(* Clients with pending requests that are not scheduled *)
UnscheduledClients == {c \in Clients : unsat[c] /= {} /\ c \notin ScheduledClients}

(* Position of client c in schedule, or 0 if not scheduled *)
PositionInSchedule(c) ==
    IF c \in ScheduledClients
    THEN CHOOSE i \in 1..Len(sched) : sched[i] = c
    ELSE 0

(* Resources requested by clients appearing before position p in schedule *)
ResourcesRequestedBefore(p) ==
    UNION {unsat[sched[i]] : i \in 1..(p-1)}

(* Check if resource r can be allocated to client c:
   No earlier-scheduled client has requested r *)
CanAllocate(c, r) ==
    LET pos == PositionInSchedule(c)
    IN /\ pos > 0
       /\ r \in unsat[c]
       /\ r \in AvailableResources
       /\ r \notin ResourcesRequestedBefore(pos)

(* Set of resources that can be allocated to client c *)
AllocatableResources(c) ==
    {r \in Resources : CanAllocate(c, r)}

----------------------------------------------------------------------------

(* Initial state: no requests, no allocations, empty schedule *)
Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
    /\ sched = <<>>

----------------------------------------------------------------------------

(* Actions *)

(* Client c requests a non-empty set S of resources.
   Precondition: c has no outstanding request and holds no resources *)
Request(c, S) ==
    /\ S /= {}
    /\ S \subseteq Resources
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED <<alloc, sched>>

(* Allocator allocates resource r to client c *)
Allocate(c, r) ==
    /\ CanAllocate(c, r)
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup {r}]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ {r}]
    /\ UNCHANGED sched

(* Client c returns a non-empty set S of resources it holds.
   If c's request is fully satisfied (unsat[c] = {}), c must eventually return all.
   But c may return resources at any time. *)
Return(c, S) ==
    /\ S /= {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED <<unsat, sched>>
    
(* Remove client c from schedule when c has no outstanding request *)
RemoveFromSchedule(c) ==
    /\ c \in ScheduledClients
    /\ unsat[c] = {}
    /\ LET pos == PositionInSchedule(c)
       IN sched' = SubSeq(sched, 1, pos-1) \o SubSeq(sched, pos+1, Len(sched))
    /\ UNCHANGED <<unsat, alloc>>

(* Extend schedule by appending a permutation of unscheduled clients with pending requests *)
RECURSIVE SeqToSet(_)
SeqToSet(s) ==
    IF s = <<>> THEN {}
    ELSE {Head(s)} \cup SeqToSet(Tail(s))

RECURSIVE Perms(_)
Perms(S) ==
    IF S = {} THEN {<<>>}
    ELSE UNION {{<<x>> \o p : p \in Perms(S \ {x})} : x \in S}

ExtendSchedule(perm) ==
    /\ perm \in Perms(UnscheduledClients)
    /\ perm /= <<>>
    /\ sched' = sched \o perm
    /\ UNCHANGED <<unsat, alloc>>

----------------------------------------------------------------------------

(* Next state relation *)
Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, r \in Resources : Allocate(c, r)
    \/ \E c \in Clients, S \in SUBSET Resources : Return(c, S)
    \/ \E c \in Clients : RemoveFromSchedule(c)
    \/ \E perm \in Perms(UnscheduledClients) : ExtendSchedule(perm)

----------------------------------------------------------------------------

(* Safety Properties *)

(* Resources are allocated exclusively: no resource held by two clients *)
Mutex ==
    \A c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

(* All clients in schedule have outstanding requests *)
ScheduledClientsHaveRequests ==
    \A c \in ScheduledClients : unsat[c] /= {} \/ alloc[c] /= {}

(* Stronger version: scheduled clients have unsatisfied resources *)
ScheduleCorrect ==
    \A c \in ScheduledClients : unsat[c] /= {}

(* The allocator can satisfy each scheduled client's request assuming 
   earlier-scheduled clients eventually release their resources.
   This means: for each scheduled client, the resources they need exist
   and are either available or held by later-scheduled clients. *)
CanSatisfyScheduled ==
    \A i \in 1..Len(sched) :
        LET c == sched[i]
            laterClients == {sched[j] : j \in (i+1)..Len(sched)}
            laterAlloc == UNION {alloc[x] : x \in laterClients}
        IN unsat[c] \subseteq (AvailableResources \cup laterAlloc \cup alloc[c])

(* Combined safety property *)
Safety ==
    /\ Mutex
    /\ ScheduleCorrect
    /\ CanSatisfyScheduled

----------------------------------------------------------------------------

(* Fairness conditions *)

(* Allocator eventually schedules pending clients *)
SchedulingFairness ==
    WF_vars(\E perm \in Perms(UnscheduledClients) : ExtendSchedule(perm))

(* Allocator eventually allocates available resources *)
AllocationFairness ==
    \A c \in Clients, r \in Resources :
        WF_vars(Allocate(c, r))

(* Clients eventually return all held resources once fully satisfied *)
ReturnFairness ==
    \A c \in Clients :
        WF_vars(\E S \in SUBSET alloc[c] : S /= {} /\ unsat[c] = {} /\ Return(c, S))

(* Combined fairness *)
Fairness ==
    /\ SchedulingFairness
    /\ AllocationFairness
    /\ ReturnFairness

----------------------------------------------------------------------------

(* Liveness Properties *)

(* Every client obtains each requested resource eventually *)
ClientGetsRequested ==
    \A c \in Clients, r \in Resources :
        (r \in unsat[c]) ~> (r \in alloc[c])

(* Every satisfied client eventually releases all resources *)
SatisfiedClientReturns ==
    \A c \in Clients :
        (unsat[c] = {} /\ alloc[c] /= {}) ~> (alloc[c] = {})

(* Every client is fully satisfied infinitely often 
   (has received all requested resources and returned them) *)
ClientSatisfiedInfinitelyOften ==
    \A c \in Clients :
        []<>(unsat[c] = {} /\ alloc[c] = {})

(* Combined liveness *)
Liveness ==
    /\ ClientGetsRequested
    /\ SatisfiedClientReturns
    /\ ClientSatisfiedInfinitelyOften

----------------------------------------------------------------------------

(* Specification *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Safety
THEOREM Spec => Liveness

============================================================================