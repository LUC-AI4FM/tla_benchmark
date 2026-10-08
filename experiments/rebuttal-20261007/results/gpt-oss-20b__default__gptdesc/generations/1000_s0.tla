MODULE ResourceAllocator
EXTENDS Naturals, Sequences, TLC

CONSTANTS Clients, Resources

VARIABLES owned, pending, available

(* Type correctness *)
TypeOK == 
  /\ owned ∈ [Clients -> SUBSET Resources]
  /\ pending ∈ [Clients -> SUBSET Resources]
  /\ available ⊆ Resources

(* Initial state *)
Init ==
  /\ owned   = [c \in Clients |-> {}]
  /\ pending = [c \in Clients |-> {}]
  /\ available = Resources

(* Actions *)

Request(c, R) == 
  /\ c ∈ Clients
  /\ R ⊆ Resources
  /\ owned[c] = {}
  /\ pending[c] = {}
  /\ pending'   = [pending EXCEPT ![c] = R]
  /\ UNCHANGED <<owned, available>>

Allocate(c, r) ==
  /\ c ∈ Clients
  /\ r ∈ Resources
  /\ r ∈ pending[c]
  /\ r ∈ available
  /\ owned'     = [owned   EXCEPT ![c] = owned[c] \cup {r}]
  /\ pending'   = [pending EXCEPT ![c] = pending[c] \ {r}]
  /\ available' = available \ {r}

Return(c, S) ==
  /\ c ∈ Clients
  /\ S ⊆ owned[c]
  /\ owned'     = [owned   EXCEPT ![c] = owned[c] \ S]
  /\ pending'   = [pending EXCEPT ![c] = pending[c] \ S]
  /\ available' = available ∪ S

Next ==
  \/ ∃ c ∈ Clients, R ⊆ Resources : Request(c,R)
  \/ ∃ c ∈ Clients, r ∈ Resources : Allocate(c,r)
  \/ ∃ c ∈ Clients, S ⊆ owned[c] : Return(c,S)

(* Mutual exclusion of resource ownership *)
MutualExclusion ==
  ∀ r ∈ Resources :
    # { c ∈ Clients : r ∈ owned[c] } <= 1

(* Eventual return property: every allocated resource will eventually be returned *)
EventualReturn ==
  ∀ r ∈ Resources :
    (∃ c ∈ Clients : r ∈ owned[c]) => <> (∀ c' ∈ Clients : r ∉ owned[c'])

(* Eventual obtainment property: each request will eventually be satisfied *)
EventualObtainment ==
  ∀ c ∈ Clients :
    pending[c] ≠ {} => <> (pending[c] = {})

(* Infinitely often no unsatisfied requests *)
InfNoUnsatisfied ==
  []<> (∀ c ∈ Clients : pending[c] = {})

(* Symmetry expression placeholder *)
SymmetryExpr ==
  ∀ c1, c2 ∈ Clients :
    (owned[c1] = owned[c2]) /\ (pending[c1] = pending[c2]) => TRUE

(* Concrete counterexample value structure *)
CounterExample == [client |-> "c1", reqResources |-> {"r1","r2"}, returnedResources |-> {"r1"}]

vars == <<owned, pending, available>>

SpecWF ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

SpecSF ==
  Init /\ [][Next]_vars /\ SF_vars(Next)

(* Final specification *)
Spec == SpecWF

Safety == TypeOK /\ MutualExclusion
Liveness == EventualReturn /\ EventualObtainment /\ InfNoUnsatisfied

END MODULE