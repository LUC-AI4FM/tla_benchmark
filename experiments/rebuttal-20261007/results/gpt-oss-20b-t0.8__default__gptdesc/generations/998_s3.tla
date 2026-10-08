MODULE ResourceAllocator
EXTENDS Naturals, Sequences

CONSTANTS RESOURCES, CLIENTS, SCHED_LIST

VARIABLE holds, requests, schedIdx

(* Type invariant *)
TypeInv == /\ holds \in [CLIENTS -> SUBSET RESOURCES]
          /\ requests \in [CLIENTS -> SUBSET RESOURCES]
          /\ schedIdx \in 1..Len(SCHED_LIST)
          /\ SCHED_LIST \in Seq(CLIENTS)

Init == /\ holds = [c ∈ CLIENTS |-> {}]
        /\ requests = [c ∈ CLIENTS |-> {}]
        /\ schedIdx = 1

Request ==
  \E c ∈ CLIENTS, newReq ⊆ RESOURCES :
    /\ newReq /= {}
    /\ holds[c] = {}
    /\ requests[c] = {}
    /\ requests' = [requests EXCEPT ![c] = newReq]
    /\ UNCHANGED <<holds, schedIdx>>

Serve ==
  \E c ∈ CLIENTS, r ∈ RESOURCES :
    /\ c = SCHED_LIST[schedIdx]
    /\ r ∈ requests[c]
    /\ \A d ∈ CLIENTS \ {c} : r ∉ holds[d]
    /\ holds' = [holds EXCEPT ![c] = holds[c] ∪ {r}]
    /\ requests' = [requests EXCEPT ![c] = requests[c] \ {r}]
    /\ schedIdx' = IF schedIdx < Len(SCHED_LIST) THEN schedIdx + 1 ELSE 1
    /\ UNCHANGED <<>>

ReturnStep ==
  \E c ∈ CLIENTS, returnSet ⊆ holds[c] :
    /\ holds' = [holds EXCEPT ![c] = holds[c] \ returnSet]
    /\ UNCHANGED <<requests, schedIdx>>

IdleStep ==
  /\ ¬(\E c ∈ CLIENTS, r ∈ RESOURCES :
          c = SCHED_LIST[schedIdx]
          /\ r ∈ requests[c]
          /\ \A d ∈ CLIENTS \ {c} : r ∉ holds[d])
  /\ schedIdx' = IF schedIdx < Len(SCHED_LIST) THEN schedIdx + 1 ELSE 1
  /\ UNCHANGED <<holds, requests>>

Next == Request \/ Serve \/ ReturnStep \/ IdleStep

(* Mutual exclusion invariant *)
MutExcl == \A r ∈ RESOURCES :
            \E!c1 c2 ∈ CLIENTS : (r ∈ holds[c1] /\ r ∈ holds[c2]) => c1 = c2

(* Client request/hold consistency *)
ReqHoldInv ==
  \A c ∈ CLIENTS :
    ((requests[c] /= {} /\ holds[c] = {}) /\ (holds[c] /= {} /\ requests[c] = {}))

Spec == Init
        /\ [][Next]_<<holds, requests, schedIdx>>
        /\ WF_Serve
        /\ WF_ReturnStep
        /\ WF_IdleStep
        /\ TypeInv
        /\ MutExcl
        /\ ReqHoldInv
        /\ \A c ∈ CLIENTS :
            []((requests[c] = {} /\ holds[c] /= {}) => <> (holds[c] = {}))
        /\ \A c ∈ CLIENTS :
            []((requests[c] /= {}) => <> (requests[c] = {}))
        /\ \A c ∈ CLIENTS :
