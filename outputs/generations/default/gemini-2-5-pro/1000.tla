-------------------------- MODULE ResourceAllocator --------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Resources, Clients

ASSUME IsFinite(Resources) /\ IsFinite(Clients)

\* A concrete value structure for model checking.
\* A counterexample to liveness properties can be found with these values
\* if fairness is not assumed. For example, if c1 requests and is granted r1,
\* and c2 then requests r1, c2 will wait forever if c1 never returns r1.
\* CONSTANTS
\*  Resources = {r1}
\*  Clients = {c1, c2}

VARIABLES held, req

vars == <<held, req>>

(***************************************************************************)
(*                         State Constraints                               *)
(***************************************************************************)
TypeOK ==
    /\ held \in [Clients -> SUBSET Resources]
    /\ req \in [Clients -> SUBSET Resources]

\* The set of resources not currently held by any client.
available == Resources \ UNION {held[c] : c \in Clients}

\* Mutual exclusion: a resource is held by at most one client.
MutualExclusion ==
    \A c1, c2 \in Clients : c1 # c2 => held[c1] \cap held[c2] = {}

(***************************************************************************)
(*                           System Actions                                *)
(***************************************************************************)

\* The initial state: no resources are held, no requests are pending.
Init ==
    /\ held = [c \in Clients |-> {}]
    /\ req  = [c \in Clients |-> {}]

\* A client `c` requests a non-empty set of resources `S`.
\* This is only allowed if `c` holds no resources and has no pending request.
Request(c, S) ==
    /\ held[c] = {}
    /\ req[c] = {}
    /\ S \subseteq Resources /\ S # {}
    /\ req' = [req EXCEPT ![c] = S]
    /\ held' = held

\* The system grants an available resource `r` to a client `c` that requested it.
Grant(c, r) ==
    /\ r \in req[c]
    /\ r \in available
    /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
    /\ req'  = [req EXCEPT ![c] = req[c] \ {r}]

\* A client `c` returns a resource `r` that it holds.
Return(c, r) ==
    /\ r \in held[c]
    /\ held' = [held EXCEPT ![c] = held[c] \ {r}]
    /\ req' = req

\* The next-state relation.
Next ==
    \/ \E c \in Clients, S \in SUBSET Resources : Request(c, S)
    \/ \E c \in Clients, r \in Resources : Grant(c, r)
    \/ \E c \in Clients, r \in Resources : Return(c, r)

(***************************************************************************)
(*                     Temporal Specifications                             *)
(***************************************************************************)

\* The first system specification without any fairness assumptions.
Spec == Init /\ [][Next]_vars

\* Fairness assumptions.
\* - Weak fairness on Return: If a client can return a resource, it eventually will.
\*   (WF is sufficient because once enabled, Return(c,r) stays enabled).
\* - Strong fairness on Grant: If a client has an outstanding request for a resource
\*   that becomes available infinitely often, it will eventually be granted.
\*   (SF is needed because the resource might be granted to other clients).
Fairness ==
    /\ \A c \in Clients, r \in Resources : WF_vars(Return(c, r))
    /\ \A c \in Clients, r \in Resources : SF_vars(Grant(c, r))

\* The second system specification, including fairness.
FairSpec == Spec /\ Fairness

(***************************************************************************)
(*                             Properties                                  *)
(***************************************************************************)

\* The safety properties hold for the base specification.
THEOREM Spec => [](TypeOK /\ MutualExclusion)

\* If a client holds resources, it will eventually return all of them.
EventualReturn(c) == held[c] # {} ~> held[c] = {}

\* If a client has an unsatisfied request, it will eventually obtain all resources.
EventualObtain(c) == req[c] # {} ~> req[c] = {}

\* Each client is infinitely often in a state with no unsatisfied request.
InfinitelyOftenNoRequest(c) == []<>(req[c] = {})

\* The liveness properties are expected to hold under the fairness assumptions.
THEOREM FairSpec => \A c \in Clients : EventualReturn(c)
THEOREM FairSpec => \A c \in Clients : EventualObtain(c)
THEOREM FairSpec => \A c \in Clients : InfinitelyOftenNoRequest(c)

(***************************************************************************)
(*                             Symmetry                                    *)
(***************************************************************************)

\* This section defines the symmetry sets for this specification. The system
\* state is symmetric under any permutation of Clients and Resources. This
\* can be used by a model checker to reduce the state space.

Permutations(S) == {p \in [S -> S] : \A x, y \in S : (p[x] = p[y]) => (x = y)}

ClientPerms == Permutations(Clients)
ResourcePerms == Permutations(Resources)

SymmetrySet == {<<p_c, p_r>> : p_c \in ClientPerms, p_r \in ResourcePerms}

=============================================================================