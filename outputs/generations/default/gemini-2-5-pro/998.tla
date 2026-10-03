------------------------ MODULE ResourceAllocator ------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Clients, Resources

ASSUME    /\ IsFiniteSet(Clients)
          /\ IsFiniteSet(Resources)
          /\ Clients /= {}

VARIABLES requests, held, schedule

vars == <<requests, held, schedule>>

-----------------------------------------------------------------------------
\* Type invariant for the state variables.
TypeOK ==
    /\ requests \in [Clients -> SUBSET Resources]
    /\ held \in [Clients -> SUBSET Resources]
    /\ IsAPermutation(schedule, Clients)

\* The set of resources not currently held by any client.
Available == Resources \ \bigcup {held[c] : c \in Clients}

-----------------------------------------------------------------------------
\* System Actions

\* A client c requests a non-empty set of resources r.
\* This is enabled only if the client has no outstanding requests and holds no resources.
Request(c, r) ==
    /\ requests[c] = {}
    /\ held[c] = {}
    /\ r \subseteq Resources
    /\ r /= {}
    /\ requests' = [requests EXCEPT ![c] = r]
    /\ UNCHANGED <<held, schedule>>

\* The allocator grants a non-empty set of available resources g to client c.
\* This is enabled only if c is at the head of the schedule and has an outstanding request.
Grant(c, g) ==
    /\ schedule /= <<>>
    /\ Head(schedule) = c
    /\ g \subseteq requests[c]
    /\ g /= {}
    /\ g \subseteq Available
    /\ requests' = [requests EXCEPT ![c] = @ \setminus g]
    /\ held' = [held EXCEPT ![c] = @ \cup g]
    /\ UNCHANGED <<schedule>>

\* A client c may return a non-empty subset r of its held resources at any time.
EarlyReturn(c, r) ==
    /\ r \subseteq held[c]
    /\ r /= {}
    /\ held' = [held EXCEPT ![c] = @ \setminus r]
    /\ UNCHANGED <<requests, schedule>>

\* A client c that is fully satisfied (i.e., its request set is empty)
\* must eventually return all resources it holds.
SatisfiedReturn(c) ==
    /\ requests[c] = {}
    /\ held[c] /= {}
    /\ held' = [held EXCEPT ![c] = {}]
    /\ UNCHANGED <<requests, schedule>>

\* The scheduler moves the client at the head of the schedule to the tail.
Reschedule ==
    /\ schedule /= <<>>
    /\ schedule' = Tail(schedule) \o <<Head(schedule)>>
    /\ UNCHANGED <<requests, held>>

-----------------------------------------------------------------------------
\* Specification

Init ==
    /\ requests = [c \in Clients |-> {}]
    /\ held = [c \in Clients |-> {}]
    /\ IsAPermutation(schedule, Clients)

Next ==
    \/ \E c \in Clients, r \in SUBSET Resources : Request(c, r)
    \/ \E c \in Clients, g \in SUBSET Resources : Grant(c, g)
    \/ \E c \in Clients, r \in SUBSET Resources : EarlyReturn(c, r)
    \/ \E c \in Clients : SatisfiedReturn(c)
    \/ Reschedule

\* Fairness ensures that progress is made.
Fairness ==
    /\ \A c \in Clients : WF_vars(SatisfiedReturn(c))
    /\ WF_vars(\E c \in Clients, g \in SUBSET Resources : Grant(c, g))
    /\ WF_vars(Reschedule)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Properties and Invariants to be checked by TLC

\* No two clients hold the same resource.
MutualExclusion ==
    \A c1, c2 \in Clients : c1 /= c2 => held[c1] \cap held[c2] = {}

\* The set of all held and all available resources is the set of all resources.
ResourcesPartitioned ==
    \bigcup {held[c] : c \in Clients} \cup Available = Resources
    /\ \bigcup {held[c] : c \in Clients} \cap Available = {}

\* A client that is fully satisfied and holds resources eventually returns them.
EventualReturn ==
    \A c \in Clients: (requests[c] = {} /\ held[c] /= {}) ~> (held'[c] = {})

\* A client with an outstanding request eventually has it fully satisfied.
EventualObtainment ==
    \A c \in Clients : (requests[c] /= {}) ~> (requests'[c] = {})

\* A client that infinitely often has a request is infinitely often satisfied.
InfinitelyOftenSatisfied ==
    \A c \in Clients :
        ([]<>(requests[c] /= {})) => ([]<>(requests[c] = {}))

=============================================================================