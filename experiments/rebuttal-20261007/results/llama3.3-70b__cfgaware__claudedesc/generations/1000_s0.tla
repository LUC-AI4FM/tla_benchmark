---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Clients, Resources

VARIABLE unsat, alloc

Init == (* Initial condition *)
        /\ unsat = [c \in Clients |-> {}]
        /\ alloc = [c \in Clients |-> {}]

Request(c, S) == (* Client c requests resources in set S *)
        /\ c \in Clients
        /\ S \subseteq Resources
        /\ S /= {}
        /\ unsat' = [unsat EXCEPT ![c] = S]
        /\ alloc' = alloc

Allocate(c, S) == (* Allocator grants client c resources in set S *)
        /\ c \in Clients
        /\ S \subseteq Resources
        /\ S /= {}
        /\ S \subseteq (Resources \cup {r \in Resources: ∀d ∈ Clients : r ∉ alloc[d]})
        /\ S \subseteq unsat[c]
        /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]

Return(c, S) == (* Client c returns resources in set S *)
        /\ c \in Clients
        /\ S \subseteq Resources
        /\ S /= {}
        /\ S \subseteq alloc[c]
        /\ unsat' = unsat
        /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]

Next == (* Next-state relation *)
        \/ \E c \in Clients, S \subseteq Resources : Request(c, S)
        \/ \E c \in Clients, S \subseteq Resources : Allocate(c, S)
        \/ \E c \in Clients, S \subseteq Resources : Return(c, S)

SimpleAllocator == (* Principal specification *)
        Init /\ [][Next]_unsat,alloc
        /\ WF(Next, Return) (* Weak fairness on returns *)
        /\ SF(Next, Allocate) (* Strong fairness on allocations *)

SimpleAllocator2 == (* Weaker variant of the principal specification *)
        Init /\ [][Next]_unsat,alloc
        /\ \A c \in Clients : WF(Next, Return(c, unsat[c])) (* Weak fairness on returns after full request satisfaction *)
        /\ SF(Next, Allocate) (* Strong fairness on allocations *)

TypeInvariant == (* Type invariant: unsat and alloc are sets of resources for each client *)
        \A c \in Clients : unsat[c] \subseteq Resources
        /\ \A c \in Clients : alloc[c] \subseteq Resources

ResourceMutex == (* Resource mutex: no two clients hold the same resource simultaneously *)
        \A r \in Resources : \A c1, c2 \in Clients : c1 /= c2 => ~(r \in alloc[c1] /\ r \in alloc[c2])

ClientsWillReturn == (* Liveness property: clients eventually release resources once satisfied *)
        \A c \in Clients : <>[]<>(unsat[c] = {})

ClientsWillObtain == (* Liveness property: every requested resource is eventually allocated *)
        \A c \in Clients, r \in Resources : unsat[c] = {r} => <>[]<>(r \in alloc[c])

InfOftenSatisfied == (* Liveness property: every client is satisfied infinitely often *)
        \A c \in Clients : []<>unsat[c] = {}

THEOREM SimpleAllocator2 => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied

=============================================================================