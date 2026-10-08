----------------------------- MODULE KeyValueStore -----------------------------
EXTENDS FiniteSets

CONSTANTS KEYS, VALS, MISSING
ASSUME KEYS \in SUBSET 0..10 /\ VALS \in SUBSET 1..20 /\ 
       MISSING \notin Vals /\ MISSING \notin KEYS

Ops == {"get", "insert", "update", "delete"}

VARIABLES store, currentOp, keyArg, valArg, retVal, ready, working

(*--- Type Invariants -----------------------------------------------------*)
TypeInv ==
  /\ store \in [k \in KEYS |-> Vals \/ {MISSING}]
  /\ currentOp \in Ops \/ {"none"}
  /\ keyArg \in KEYS
  /\ valArg \in Vals
  /\ retVal \in Vals \/ {MISSING}
  /\ ready \in BOOLEAN
  /\ working \in BOOLEAN
  /\ (ready => ~working)
  /\ (working => ~ready)

(*--- Initial State --------------------------------------------------------*)
Init ==
  /\ store = [k \in KEYS |-> MISSING]
  /\ currentOp = "none"
  /\ ready = TRUE
  /\ working = FALSE
  /\ keyArg \in KEYS
  /\ valArg \in Vals
  /\ retVal \in Vals \/ {MISSING}

(*--- Request Actions -----------------------------------------------------*)
RequestGet(k) ==
  /\ ready
  /\ currentOp = "none"
  /\ keyArg' = k
  /\ valArg' = valArg
  /\ currentOp' = "get"
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ store' = store
  /\ retVal' = retVal

RequestInsert(k, v) ==
  /\ ready
  /\ currentOp = "none"
  /\ keyArg' = k
  /\ valArg' = v
  /\ currentOp' = "insert"
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ store' = store
  /\ retVal' = retVal

RequestUpdate(k, v) ==
  /\ ready
  /\ currentOp = "none"
  /\ keyArg' = k
  /\ valArg' = v
  /\ currentOp' = "update"
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ store' = store
  /\ retVal' = retVal

RequestDelete(k) ==
  /\ ready
  /\ currentOp = "none"
  /\ keyArg' = k
  /\ valArg' = valArg
  /\ currentOp' = "delete"
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ store' = store
  /\ retVal' = retVal

(*--- Response Actions ----------------------------------------------------*)
ResponseGet ==
  /\ working
  /\ currentOp = "get"
  /\ retVal' = store[keyArg]
  /\ currentOp' = "none"
  /\ working' = FALSE
  /\ ready' = TRUE
  /\ store' = store
  /\ keyArg' = keyArg
  /\ valArg' = valArg

ResponseInsert ==
  /\ working
  /\ currentOp = "insert"
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retVal' = retVal
  /\ currentOp' = "none"
  /\ working' = FALSE
  /\ ready' = TRUE
  /\ keyArg' = keyArg
  /\ valArg' = valArg

ResponseUpdate ==
  /\ working
  /\ currentOp = "update"
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retVal' = retVal
  /\ currentOp' = "none"
  /\ working' = FALSE
  /\ ready' = TRUE
  /\ keyArg' = keyArg
  /\ valArg' = valArg

ResponseDelete ==
  /\ working
  /\ currentOp = "delete"
  /\ store' = [store EXCEPT ![keyArg] = MISSING]
  /\ retVal' = retVal
  /\ currentOp' = "none"
  /\ working' = FALSE
  /\ ready' = TRUE
  /\ keyArg' = keyArg
  /\ valArg' = valArg

(*--- Skip action for stuttering ----------------------------------------*)
Skip ==
  UNCHANGED <<store, currentOp, keyArg, valArg, retVal, ready, working>>

(*--- Next-state relation -------------------------------------------------*)
Next == 
  RequestGet \lor
  RequestInsert \lor
  RequestUpdate \lor
  RequestDelete \lor
  ResponseGet \lor
  ResponseInsert \lor
  ResponseUpdate \lor
  ResponseDelete \lor
  Skip

(*--- Delete request action used for fairness ---------------------------------*)
DeleteReq ==
  ∃ k \in KEYS : RequestDelete(k)

(*--- Specification --------------------------------------------------------*)
Spec == Init /\ []Next /\ WF_vars(DeleteReq) /\ TypeInv
====================================================================