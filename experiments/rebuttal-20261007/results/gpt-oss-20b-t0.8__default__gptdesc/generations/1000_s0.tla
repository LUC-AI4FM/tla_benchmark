MODULE ResourceAllocator
EXTENDS Naturals, Sequences, SETS

CONSTANTS Clients, Resources

VARIABLES holds, pending

vars == {holds, pending}

(* Type correctness *)
TypeOK ==
  /\ holds ∈ [Clients -> SUBSET Resources]
  /\ pending ∈ [Clients -> SUBSET Resources]

(* Mutual exclusion of resource ownership *)
MutualExclusion ==
  ∀ r ∈ Resources :
    #({c ∈ Clients : r ∈ holds[c]}) <= 1

(* No overlap between held and pending resources for a client *)
NoOverlap ==
  ∀ c ∈ Clients : holds[c] ∩ pending[c] = {}

SafetyInv == TypeOK /\ MutualExclusion /\ NoOverlap

(* Request: a client that holds nothing and has no pending request may issue a new request *)
Request ==
  ∃ c ∈ Clients, rset ⊆ Resources :
    /\ holds[c] = {}
    /\ pending[c] = {}
    /\ pending' = [pending EXCEPT ![c] = rset]
    /\ UNCHANGED holds

(* Allocate: a client may be granted any subset of its pending resources that are currently free *)
Allocate ==
  ∃ c ∈ Clients, aset ⊆ pending[c] :
    /\ aset ⊆ (Resources \ {r | ∃ d ∈ Clients : d #= c /\ r ∈ holds[d]})
    /\ holds' = [holds EXCEPT ![c] = holds[c] ∪ aset]
    /\ pending' = [pending EXCEPT ![c] = pending[c] \ aset]

(* Release: a client may return any subset of the resources it currently holds *)
Release ==
  ∃ c ∈ Clients, sset ⊆ holds[c] :
    /\ holds' = [holds EXCEPT ![c] = holds[c] \ sset]
    /\ UNCHANGED pending

Next == Request \/ Allocate \/ Release

Init == 
  /\ holds = [c ∈ Clients |-> {}]
  /\ pending = [c ∈ Clients |-> {}]

(* Liveness properties *)

EventualRelease(c) ==
  □(∃ r ∈ holds[c] ⇒ ◇(holds[c] = {}))

EventualObtainment(c, r) ==
  □(r ∈ pending[c] ⇒ ◇(r ∈ holds[c]))

InfiniteNoPending ==
  □◇(∀ c ∈ Clients : pending[c] = {})

LivenessProps ==
  ∧ ∀ c ∈ Clients : EventualRelease(c)
  ∧ ∀ c ∈ Clients, r ∈ Resources : EventualObtainment(c, r)
  ∧ InfiniteNoPending

(* Fairness assumptions *)
Fairness == 
  WF_Act(Request, vars) 
  /\ WF_Act(Allocate, vars) 
  /\ WF_Act(Release, vars)

Spec ==
  Init
  /\ [][Next]_vars
  /\ SafetyInv
  /\ Fairness
  /\ LivenessProps

(* Symmetry expression (the system treats all clients identically) *)
SymmetryExpr == 
  ∀ c,d ∈ Clients :
    (c #= d) => (holds[c] = holds[d]) /\ (pending[c] = pending[d])

(* Concrete counterexample value structure showing a violation of mutual exclusion *)
Counterexample ==
  << holds := [c ∈ Clients |-> {"R1"}],
     pending := [c ∈ Clients |-> {}] >>

END ResourceAllocator