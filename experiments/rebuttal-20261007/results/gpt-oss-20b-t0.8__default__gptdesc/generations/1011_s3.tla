--------------------------- MODULE KVStore ---------------------------
EXTENDS Integers, TLC

CONSTANTS KEYS, VALUES, MISSING, NULL

(* Type Definitions *)
TYPEDEF
  KeySet == [k ∈ KEYS |-> VALUES ∪ {MISSING}]

VARIABLES
  store, op, key, val, ret, ready, working

Ops == {"GET","INSERT","UPDATE","DELETE", "NONE"}

(* Safety Invariant: type correctness of all state variables *)
TypeOK ==
  /\ store ∈ [KEYS -> VALUES ∪ {MISSING}]
  /\ op ∈ Ops
  /\ key ∈ KEYS ∪ {NULL}
  /\ val ∈ VALUES ∪ {NULL}
  /\ ret ∈ VALUES ∪ {MISSING, NULL}
  /\ ready ∈ BOOLEAN
  /\ working ∈ BOOLEAN

(* Initial State *)
Init ==
  /\ store = [k ∈ KEYS |-> MISSING]
  /\ op = "NONE"
  /\ key = NULL
  /\ val = NULL
  /\ ret = NULL
  /\ ready = TRUE
  /\ working = FALSE

(* Request Actions *)
GetReq(k) == 
  /\ ready
  /\ op'   = "GET"
  /\ key'  = k
  /\ val'  = NULL
  /\ ret'  = NULL
  /\ ready'= FALSE
  /\ working'= TRUE
  /\ UNCHANGED store

InsertReq(k,v) ==
  /\ ready
  /\ op'   = "INSERT"
  /\ key'  = k
  /\ val'  = v
  /\ ret'  = NULL
  /\ ready'= FALSE
  /\ working'= TRUE
  /\ UNCHANGED store

UpdateReq(k,v) ==
  /\ ready
  /\ op'   = "UPDATE"
  /\ key'  = k
  /\ val'  = v
  /\ ret'  = NULL
  /\ ready'= FALSE
  /\ working'= TRUE
  /\ UNCHANGED store

DeleteReq(k) ==
  /\ ready
  /\ op'   = "DELETE"
  /\ key'  = k
  /\ val'  = NULL
  /\ ret'  = NULL
  /\ ready'= FALSE
  /\ working'= TRUE
  /\ UNCHANGED store

(* Response Actions *)
GetResp ==
  /\ working
  /\ op = "GET"
  /\ ret'   = IF (store[key] # MISSING) THEN store[key] ELSE MISSING
  /\ UNCHANGED store
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = "NONE"
  /\ key'     = NULL
  /\ val'     = NULL

InsertResp ==
  /\ working
  /\ op = "INSERT"
  /\ store' = [store EXCEPT ![key] = val]
  /\ ret'   = NULL
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = "NONE"
  /\ key'     = NULL
  /\ val'     = NULL

UpdateResp ==
  /\ working
  /\ op = "UPDATE"
  /\ store' = [store EXCEPT ![key] = val]
  /\ ret'   = NULL
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = "NONE"
  /\ key'     = NULL
  /\ val'     = NULL

DeleteResp ==
  /\ working
  /\ op = "DELETE"
  /\ store' = [store EXCEPT ![key] = MISSING]
  /\ ret'   = NULL
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = "NONE"
  /\ key'     = NULL
  /\ val'     = NULL

(* Stuttering Action *)
Stutter ==
  UNCHANGED <<store,op,key,val,ret,ready,working>>

Next ==
  \/ ∃k ∈ KEYS: GetReq(k)
  \/ ∃k ∈ KEYS, v ∈ VALUES: InsertReq(k,v)
  \/ ∃k ∈ KEYS, v ∈ VALUES: UpdateReq(k,v)
  \/ ∃k ∈ KEYS: DeleteReq(k)
  \/ GetResp
  \/ InsertResp
  \/ UpdateResp
  \/ DeleteResp
  \/ Stutter

(* Liveness Property: Weak fairness for delete responses *)
Liveness == WF_1(DeleteResp)

(* Speculation of the system behavior *)
Spec ==
  Init
  /\ [][Next]_(store,op,key,val,ret,ready,working)
  /\ Liveness
  /\ TypeOK

=============================================================================