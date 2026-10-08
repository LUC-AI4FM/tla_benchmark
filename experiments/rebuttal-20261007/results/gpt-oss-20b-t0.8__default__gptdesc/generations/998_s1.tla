------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Clients, Resources, ScheduleOrder \* a permutation of Clients

VARIABLES alloc, holds, requested, schedule

(* Derived definitions *)
Free(r) == alloc[r] = "free"
Pending(c) == requested[c] \ { r \in Resources : Free(r) }

(* Type invariant *)
TypeInv ==
    /\ alloc \in [Resources -> Clients \cup {"free"}]
    /\ holds \in [Clients -> SUBSET Resources]
    /\ requested \in [Clients -> SUBSET Resources]
    /\ schedule \in Seq(Clients)

(* Allocator invariants *)
AllocInvariant ==
    (* each resource is either free or allocated to one client *)
    ∀ r \in Resources : alloc[r] = "free" \/ (∃ c \in Clients : alloc[r] = c)

HoldsInvariant ==
    holds = [c \in Clients |-> { r \in Resources : alloc[r] = c }]

RequestedInvariant ==
    (* a client never holds resources it did not request *)
    ∀ c \in Clients : holds[c] ⊆ requested[c]

(* Initial state *)
Init ==
    /\ alloc = [r \in Resources |-> "free"]
    /\ holds = [c \in Clients |-> {}]
    /\ requested = [c \in Clients |-> {}]
    /\ schedule = ScheduleOrder

(* Request action: client issues a new request when holding none and no pending *)
Request(c, R) ==
    /\ c \in Clients
    /\ holds[c] = {}
    /\ requested[c] = {}
    /\ R ⊆ Resources
    /\ R # {}
    /\ alloc'   = alloc
    /\ holds'   = holds
    /\ requested'[c] := R
    /\ schedule' = schedule

(* Serve action: allocate free resources from the pending request of the client at head of schedule *)
Serve ==
    /\ schedule # <<>>
    /\ LET c == Head(schedule) IN
       /\ Pending(c) # {}
       /\ LET S == { r \in Pending(c) : Free(r) } IN
          /\ alloc'   = [alloc EXCEPT ![r] = c | r \in S]
          /\ holds'[c] = holds[c] ∪ S
          /\ holds'   = [d \in Clients |-> IF d = c THEN holds'[c] ELSE holds[d]]
          /\ requested'= requested
          /\ schedule' = Tail(schedule) \o <<c>>

(* Full return action, required by fairness *)
Return(c) ==
    /\ c \in Clients
    /\ holds[c] = requested[c]
    /\ ∀ r \in holds[c] : alloc'[r] = "free"
    /\ holds'   = [d \in Clients |-> IF d = c THEN {} ELSE holds[d]]
    /\ requested'= [d \in Clients |-> IF d = c THEN {} ELSE requested[d]]
    /\ schedule' = schedule

(* Early return action, optional *)
EarlyReturn(c) ==
    /\ c \in Clients
    /\ holds[c] # {}
    /\ holds[c] ⊂ requested[c]
    /\ ∀ r \in holds[c] : alloc'[r] = "free"
    /\ holds'   = [d \in Clients |-> IF d = c THEN {} ELSE holds[d]]
   