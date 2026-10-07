---- MODULE KVStore ----

EXTENDS Naturals

CONSTANTS
  Keys, Vals,
  MISSING, OK, ERR

ASSUME
  /\ Keys # {}
  /\ Vals # {}
  /\ MISSING \notin Vals
  /\ OK # ERR
  /\ OK \notin Vals
  /\ ERR \notin Vals

(*
  A simple key-value store supporting get, insert, update, and delete.
  The store maps each key to either a value in Vals or the distinguished MISSING.
  Requests/responses are modeled explicitly with:
    - op: current operation
    - argK, argV: current arguments
    - ret: return value/result
    - phase: "Ready" or "Working"
*)

CONSTANT NoOpVal
NoOp == "none"
Ops == {"get", "insert", "update", "delete"}
Phases == {"Ready", "Working"}
MVals == Vals \cup {MISSING}
Returns == MVals \cup {OK, ERR}

VARIABLES store, op, argK, argV, ret, phase

vars == << store, op, argK, argV, ret, phase >>

TypeOK ==
  /\ store \in [Keys -> MVals]
  /\ op \in Ops \cup {NoOp}
  /\ argK \in Keys
  /\ argV \in Vals
  /\ ret \in Returns
  /\ phase \in Phases
  /\ (phase = "Ready") => op = NoOp
  /\ (phase = "Working") => op \in Ops

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ phase = "Ready"
  /\ op = NoOp
  /\ \E k \in Keys: argK = k
  /\ \E v \in Vals: argV = v
  /\ ret \in Returns

(*
  Request actions: take the system from Ready to Working and set op/args.
*)
GetReq ==
  /\ phase = "Ready"
  /\ op = NoOp
  /\ \E k \in Keys:
       /\ argK' = k
       /\ op' = "get"
       /\ phase' = "Working"
       /\ UNCHANGED << store, argV, ret >>

InsertReq ==
  /\ phase = "Ready"
  /\ op = NoOp
  /\ \E k \in Keys, v \in Vals:
       /\ argK' = k
       /\ argV' = v
       /\ op' = "insert"
       /\ phase' = "Working"
       /\ UNCHANGED << store, ret >>

UpdateReq ==
  /\ phase = "Ready"
  /\ op = NoOp
  /\ \E k \in Keys, v \in Vals:
       /\ argK' = k
       /\ argV' = v
       /\ op' = "update"
       /\ phase' = "Working"
       /\ UNCHANGED << store, ret >>

DeleteReq ==
  /\ phase = "Ready"
  /\ op = NoOp
  /\ \E k \in Keys:
       /\ argK' = k
       /\ op' = "delete"
       /\ phase' = "Working"
       /\ UNCHANGED << store, argV, ret >>

(*
  Response actions: complete the operation, update store/ret, and go back to Ready.
*)
GetResp ==
  /\ phase = "Working"
  /\ op = "get"
  /\ ret' = store[argK]
  /\ op' = NoOp
  /\ phase' = "Ready"
  /\ UNCHANGED << store, argK, argV >>

InsertResp ==
  /\ phase = "Working"
  /\ op = "insert"
  /\ IF store[argK] = MISSING THEN
       /\ store' = [store EXCEPT ![argK] = argV]
       /\ ret' = OK
     ELSE
       /\ store' = store
       /\ ret' = ERR
  /\ op' = NoOp
  /\ phase' = "Ready"
  /\ UNCHANGED << argK, argV >>

UpdateResp ==
  /\ phase = "Working"
  /\ op = "update"
  /\ IF store[argK] # MISSING THEN
       /\ store' = [store EXCEPT ![argK] = argV]
       /\ ret' = OK
     ELSE
       /\ store' = store
       /\ ret' = ERR
  /\ op' = NoOp
  /\ phase' = "Ready"
  /\ UNCHANGED << argK, argV >>

DeleteResp ==
  /\ phase = "Working"
  /\ op = "delete"
  /\ IF store[argK] # MISSING THEN
       /\ store' = [store EXCEPT ![argK] = MISSING]
       /\ ret' = OK
     ELSE
       /\ store' = store
       /\ ret' = ERR
  /\ op' = NoOp
  /\ phase' = "Ready"
  /\ UNCHANGED << argK, argV >>

Next ==
  \/ GetReq
  \/ InsertReq
  \/ UpdateReq
  \/ DeleteReq
  \/ GetResp
  \/ InsertResp
  \/ UpdateResp
  \/ DeleteResp

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_op(DeleteReq)

THEOREM Spec => []TypeOK

====