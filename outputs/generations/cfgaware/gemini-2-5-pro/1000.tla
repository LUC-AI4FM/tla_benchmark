-------------------------- MODULE ResourceAllocator --------------------------
EXTENDS TLC, FiniteSets, Sequences

CONSTANTS Client, Resource

VARIABLES available, held, requests

vars == <<available, held, requests>>

TypeOK ==
    /\ available \in SUBSET Resource
    /\ held \in [Client -> SUBSET Resource]
    /\ requests \in [Client -> SUBSET Resource]

Init ==
    /\ available = Resource
    /\ held = [c \in Client |-> {}]
    /\ requests = [c \in Client |-> {}]

(* A client c requests a non-empty set of resources R.
   This is only allowed if the client holds no resources and has no pending requests. *)
Request(c, R) ==
    /\ held[c] = {}
    /\ requests[c] = {}
    /\ R \in (SUBSET Resource) \ {{}}
    /\ requests' = [requests EXCEPT ![c] = R]
    /\ UNCHANGED <<available, held>>

(* A client c obtains a non-empty subset S of its requested resources,
   provided those resources are available. *)
Obtain(c, S) ==
    /\ S \in (SUBSET requests[c]) \ {{}}
    /\ S \subseteq available
    /\ available' = available \ S
    /\ held' = [held EXCEPT ![c] = @ \union S]
    /\ requests' = [requests EXCEPT ![c] = @ \ S]

(* A client c returns a non-empty subset S of the resources it holds. *)
Return(c, S) ==
    /\ S \in (SUBSET held[c]) \ {{}}
    /\ available' = available \union S
    /\ held' = [held EXCEPT ![c] = @ \ S]
    /\ UNCHANGED requests

Next ==
    \/ \E c \in Client, R \in SUBSET Resource: Request(c, R)
    \/ \E c \in Client, S \in SUBSET Resource: Obtain(c, S)
    \/ \E c \in Client, S \in SUBSET Resource: Return(c, S)

Spec == Init /\ [][Next]_vars

(* Specification with weak fairness on each client's Obtain and Return actions. *)
FairSpec == Spec
    /\ \A c \in Client: WF_vars(\E S \in SUBSET Resource: Obtain(c, S))
    /\ \A c \in Client: WF_vars(\E S \in SUBSET Resource: Return(c, S))

\* PROPERTIES

(* Safety: A resource is either available or held by at most one client. *)
MutualExclusion ==
    /\ \A c1, c2 \in Client: c1 # c2 => held[c1] \cap held[c2] = {}
    /\ \A c \in Client: available \cap held[c] = {}

(* Liveness: If a client holds resources, it eventually returns all of them. *)
EventualReturn ==
    \A c \in Client: (held[c] # {}) ~> (held[c] = {})

(* Liveness: If a client requests a resource, it eventually obtains it. *)
EventualObtain ==
    \A c \in Client, r \in Resource: (r \in requests[c]) ~> (r \in held[c])

(* Liveness: Each client is infinitely often in a state with no unsatisfied requests. *)
InfinitelyOftenNoUnsatisfied ==
    \A c \in Client: []<>(requests[c] = {})

\* SYMMETRY AND COUNTEREXAMPLE

(* The system is symmetric under permutations of clients and resources. *)
Symmetry == { Permutations(Client), Permutations(Resource) }

(* A concrete value structure for model checking. *)
Client == {"c1", "c2"}
Resource == {"r1"}
Counterexample == TRUE

=============================================================================