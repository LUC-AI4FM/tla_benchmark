------------------ MODULE ResourceAllocator --------------------
EXTENDS Naturals, FiniteSets

CONSTANTS CLIENTS, RESOURCES, Null
ASSUME Null ∉ CLIENTS

VARIABLES held, request, owner

(* Type invariant *)
TypeOK == 
  /\ held   ∈ [CLIENTS -> SUBSET RESOURCES]
  /\ request∈ [CLIENTS -> SUBSET RESOURCES]
  /\ owner  ∈ [RESOURCES -> CLIENTS \cup {Null}]
  /\ ∀ r ∈ RESOURCES : owner[r] = Null \/ (owner[r] ∈ CLIENTS)

(* Initial state *)
Init == 
  /\ held   = [c ∈ CLIENTS |-> {}]
  /\ request= [c ∈ CLIENTS |-> {}]
  /\ owner  = [r ∈ RESOURCES |-> Null]

(* Client requests a set R of resources; only if no pending request and holds nothing *)
Request(c, R) ==
  /\ c ∈ CLIENTS
  /\ held[c]   = {}
  /\ request[c]= {}
  /\ R ⊆ RESOURCES
  /\ held'   = held
  /\ request'= [request EXCEPT ![c] = R]
  /\ owner'  = owner

(* Serve action: serve the minimal client with pending request *)
Serve ==
  LET pending == {d ∈ CLIENTS : request[d] ≠ {}}
      c       == CHOOSE d ∈ pending :
                 ¬∃ e ∈ pending : e < d
      avail   == {r ∈ request[c] : owner[r] = Null}
  IN
    /\ c ∈ pending
    /\ avail ≠ {}
    /\ grant ⊆ avail
    /\ grant ≠ {}
    /\ held'   = [held EXCEPT ![c] = held[c] ∪ grant]
    /\ request'= [request EXCEPT ![c] = request[c] \ grant]
    /\ owner'  = [r ∈ RESOURCES |-> IF r ∈ grant THEN c ELSE owner[r]]

(* Early return: client c returns a non‑empty subset R of held resources *)
ReturnEarly(c, R) ==
  /\ c ∈ CLIENTS
  /\ R ⊆ held[c]
  /\ R ≠ {}
  /\ held'   = [held EXCEPT ![c] = held[c] \ R]
  /\ owner'  = [r ∈ RESOURCES |-> IF r ∈ R THEN Null ELSE owner[r]]
  /\ request'= request

(* Full return: client returns all resources when fully satisfied *)
FullReturn(c) ==
  /\ c ∈ CLIENTS
  /\ request[c] = {}
  /\ held[c] ≠ {}
  /\ held'   = [held EXCEPT ![c] = {}]
  /\ owner'  = [r ∈ RESOURCES |-> IF r ∈ held[c] THEN Null ELSE owner[r]]
  /\ request'= request

Next == Request(c, R) \/ Serve \/ ReturnEarly(c, R) \/ FullReturn(c)

Spec == Init
        /\ [][Next]_vars
        /\ WF_vars[Serve]
        /\ WF_vars[FullReturn]

(* Invariants *)
MutualExcl ==
  ∀ c1, c2 ∈ CLIENTS :
    /\ c1 ≠ c2
    => held[c1] ∩ held[c2] = {}

HolderOwner ==
  ∀ c ∈ CLIENTS, r ∈ RESOURCES :
    /\ r ∈ held[c]
    => owner[r] = c

RequestInRes == 
  ∀ c ∈ CLIENTS : request[c] ⊆ RESOURCES

Inv == TypeOK /\ MutualExcl /\ HolderOwner /\ RequestInRes

(* Liveness properties *)
ReturnAfterSatisfied ==
  ∀ c ∈ CLIENTS :
    []( request[c] = {} /\ held[c] ≠ {} => <> (held[c] = {}))

ObtainAllRequested ==
  ∀ c ∈ CLIENTS :
    []( request[c] ≠ {} => <> (request[c] = {}))

THEOREM Spec ⇒ Inv
=============================================================================