---------------------------- MODULE ResourceAllocator ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Clients, Resources

VARIABLE unsat, alloc, sched

Init == (* Initial state *)
        /\ unsat = [c \in Clients |-> {}]
        /\ alloc = [c \in Clients |-> {}]
        /\ sched = << >>

Request(c, r) == (* Client c submits a new resource request *)
        /\ c \in Clients
        /\ r \subseteq Resources
        /\ r /= {}
        /\ unsat[c] = {}
        /\ alloc[c] = {}
        /\ unsat' = [unsat EXCEPT ![c] = r]
        /\ alloc' = alloc
        /\ sched' = sched

Schedule == (* Non-deterministically append a permutation of all currently unscheduled clients with pending requests to the end of the schedule sequence *)
        /\ sched' \in Perm({c \in Clients : unsat[c] /= {} \ {sched[i] : i \in 1..Len(sched)}})
        /\ alloc' = alloc
        /\ unsat' = unsat

Allocate(c) == (* Grant a subset of available, requested resources to client c *)
        /\ c \in Clients
        /\ c \in sched
        /\ unsat[c] /= {}
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup {r \in Resources : r \in unsat[c] /\ forall d \in 1..Index(sched, c) : r \notin alloc[sched[d]]}}
        /\ IF alloc'[c] \cup unsat[c] = {} THEN sched' = SubSeq(sched, 1, Index(sched, c)-1) ++ SubSeq(sched, Index(sched, c)+1, Len(sched)) ELSE sched' = sched
        /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ alloc'[c]]

Return(c, r) == (* Client c releases a subset of its held resources *)
        /\ c \in Clients
        /\ r \subseteq Resources
        /\ r \subseteq alloc[c]
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ r]
        /\ sched' = sched
        /\ unsat' = unsat

Next == (* Next-state relation *)
        \/ \E c \in Clients, r \subseteq Resources : Request(c, r)
        \/ Schedule
        \/ \E c \in Clients : Allocate(c)
        \/ \E c \in Clients, r \subseteq Resources : Return(c, r)

Spec == Init /\ [][Next]_unsat,alloc,sched

THEOREM TypeCorrectness == Spec => []TypeInvariant(unsat, alloc, sched)
THEOREM MutualExclusion == Spec => []MutualExclusionInvariant(alloc)
THEOREM AllocatorInvariant == Spec => []AllocatorInvariant(sched, unsat, alloc)
THEOREM LivenessFullReturn == Spec => WF_Return(Clients, Resources, unsat, alloc, sched)
THEOREM LivenessPartialAllocation == Spec => WF_Allocate(Clients, Resources, unsat, alloc, sched)
THEOREM LivenessScheduling == Spec => WF_Schedule(Clients, Resources, unsat, sched)

TypeInvariant(unsat, alloc, sched) ==
        /\ unsat \in [Clients -> SUBSET Resources]
        /\ alloc \in [Clients -> SUBSET Resources]
        /\ sched \in Seq(Clients)

MutualExclusionInvariant(alloc) ==
        /\ forall c1, c2 \in Clients : c1 /= c2 => alloc[c1] \cap alloc[c2] = {}

AllocatorInvariant(sched, unsat, alloc) ==
        /\ sched \subseteq Clients
        /\ forall c \in Clients : unsat[c] /= {} => c \in sched

WF_Return(Clients, Resources, unsat, alloc, sched) ==
        /\ <>(\E c \in Clients : Return(c, alloc[c]))_unsat,alloc,sched

WF_Allocate(Clients, Resources, unsat, alloc, sched) ==
        /\ <>(\E c \in Clients : Allocate(c))_unsat,alloc,sched

WF_Schedule(Clients, Resources, unsat, sched) ==
        /\ <>(Schedule)_unsat,alloc,sched
=============================================================================