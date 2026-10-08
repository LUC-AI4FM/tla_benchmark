------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Clients, Resources

VARIABLES held, request

(* --------------------------------------------------------------------------- *)
(* Type invariants *)
TypeOK == 
    /\ held ∈ [Clients → SUBSET Resources]
    /\ request ∈ [Clients → SUBSET Resources]

(* --------------------------------------------------------------------------- *)
(* Initial state: no resources allocated or requested *)
Init == 
    /\ TypeOK
    /\ \A c ∈ Clients : held[c] = {} /\ request[c] = {}

(* --------------------------------------------------------------------------- *)
(* Client submits a new request when it has none and holds nothing *)
SubmitRequest(c, R) ==
    /\ c ∈ Clients
    /\ R ⊆ Resources
    /\ R ≠ {}
    /\ request[c] = {}
    /\ held[c] = {}
    /\ request' = [request EXCEPT ![c] = R]
    /\ held'   = held

(* --------------------------------------------------------------------------- *)
(* Allocate a nonempty subset of the outstanding request that is currently available *)
Allocate(c, S) ==
    /\ c ∈ Clients
    /\ S ⊆ (request[c] \ held[c])
    /\ S ≠ {}
    /\ \A r ∈ S : \A d ∈ Clients \ {c} : r ∉ held[d]
    /\ held'   = [held EXCEPT ![c] = held[c] ∪ S]
    /\ request'= request

(* --------------------------------------------------------------------------- *)
(* Return any subset of the resources currently held *)
Return(c, T) ==
    /\ c ∈ Clients
    /\ T ⊆ held[c]
    /\ held'   = [held EXCEPT ![c] = held[c] \ T]
    /\ request'= request

(* --------------------------------------------------------------------------- *)
(* Return all resources when the request is fully satisfied *)
ReturnFull(c) ==
    /\ c ∈ Clients
    /\ request[c] = held[c]
    /\ held[c] ≠ {}
    /\ held'   = [held EXCEPT ![c] = {}]
    /\ request'= [request EXCEPT ![c] = {}]

(* --------------------------------------------------------------------------- *)
(* Next-state relation *)
Next == 
    \/ \E c ∈ Clients, R ⊆ Resources : SubmitRequest(c, R)
    \/ \E c ∈ Clients, S ⊆ Resources : Allocate(c, S)
    \/ \E c ∈ Clients, T ⊆ Resources : Return(c, T)
    \/ \E c ∈ Clients : ReturnFull(c)

(* --------------------------------------------------------------------------- *)
(* Mutual exclusion invariant: no resource is held by more than one client *)
MutualExclusion == 
    \A c1 ∈ Clients, c2 ∈ Clients :
        (c1 # c2) => held[c1] ∩ held[c2] = {}

(* --------------------------------------------------------------------------- *)
(* Specification with fairness conditions *)
Spec == Init /\ [][Next]_(held, request)
    /\ WF/LE(\E c ∈ Clients : ReturnFull(c))
    /\ SF/LE(\E c ∈ Clients, S ⊆ Resources : Allocate(c,S))

(* --------------------------------------------------------------------------- *)
(* Invariant to be proved *)
Inv == MutualExclusion

=============================================================================