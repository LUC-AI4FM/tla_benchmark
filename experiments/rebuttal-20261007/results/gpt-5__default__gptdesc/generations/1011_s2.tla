----------------------------- MODULE KeyValueStore -----------------------------

EXTENDS Naturals

CONSTANTS
  Keys,
  Vals,
  MISSING,
  OK,
  ERR,
  NoKey,
  NoVal,
  NoRet

(*
Assumptions about constants. These are not required by the spec semantics,
but help ensure type separation when model checking.
*)
ASSUME
  /\ MISSING \notin Vals
  /\ OK \notin (Vals \cup {MISSING})
  /\ ERR \notin (Vals \cup {MISSING} \cup {OK})
  /\ NoKey \notin Keys
  /\ NoVal \notin Vals
  /\ NoRet \notin (Vals \cup {MISSING} \cup {OK, ERR})

VARIABLES
  store,     \* [Keys -> Vals \cup {MISSING}]
  op,        \* current operation or NoneOp
  argK,      \* key argument
  argV,      \* value argument
  ret,       \* return value
  ready      \* boolean: TRUE = ready to accept a request, FALSE = working

(*
Operation tags
*)
GetOp    == "Get"
InsertOp == "Insert"
UpdateOp == "Update"
DeleteOp == "Delete"
NoneOp   == "None"
Ops      == {GetOp, InsertOp, UpdateOp, DeleteOp}

(*
Type correctness invariant
*)
TypeInv ==
  /\ store \in [Keys -> (Vals \cup {MISSING})]
  /\ op \in Ops \cup {NoneOp}
  /\ argK \in Keys \cup {NoKey}
  /\ argV \in Vals \cup {NoVal}
  /\ ret \in Vals \cup {MISSING} \cup {OK, ERR} \cup {NoRet}
  /\ ready \in BOOLEAN

(*
Auxiliary safety relation between ready and op
*)
ReadyWorkingInv == (ready <=> op = NoneOp)

Inv == TypeInv /\ ReadyWorkingInv

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op = NoneOp
  /\ argK = NoKey
  /\ argV = NoVal
  /\ ret = NoRet
  /\ ready = TRUE

(*
Request actions: take system from ready to working with chosen arguments.
*)

GetReq ==
  /\ ready /\ op = NoneOp
  /\ \E k \in Keys:
       /\ op' = GetOp
       /\ argK' = k
       /\ argV' = NoVal
       /\ ret' = NoRet
       /\ ready' = FALSE
       /\ store' = store

InsertReq ==
  /\ ready /\ op = NoneOp
  /\ \E k \in Keys: \E v \in Vals:
       /\ op' = InsertOp
       /\ argK' = k
       /\ argV' = v
       /\ ret' = NoRet
       /\ ready' = FALSE
       /\ store' = store

UpdateReq ==
  /\ ready /\ op = NoneOp
  /\ \E k \in Keys: \E v \in Vals:
       /\ op' = UpdateOp
       /\ argK' = k
       /\ argV' = v
       /\ ret' = NoRet
       /\ ready' = FALSE
       /\ store' = store

DeleteReq ==
  /\ ready /\ op = NoneOp
  /\ \E k \in Keys:
       /\ op' = DeleteOp
       /\ argK' = k
       /\ argV' = NoVal
       /\ ret' = NoRet
       /\ ready' = FALSE
       /\ store' = store

(*
Response actions: complete the operation and return to ready.
*)

GetResp ==
  /\ ~ready /\ op = GetOp
  /\ store' = store
  /\ ret' = store[argK]
  /\ ready' = TRUE
  /\ op' = NoneOp
  /\ argK' = NoKey
  /\ argV' = NoVal

InsertResp ==
  /\ ~ready /\ op = InsertOp
  /\ IF store[argK] = MISSING
        THEN /\ store' = [store EXCEPT ![argK] = argV]
             /\ ret' = OK
        ELSE /\ store' = store
             /\ ret' = ERR
  /\ ready' = TRUE
  /\ op' = NoneOp
  /\ argK' = NoKey
  /\ argV' = NoVal

UpdateResp ==
  /\ ~ready /\ op = UpdateOp
  /\ IF store[argK] # MISSING
        THEN /\ store' = [store EXCEPT ![argK] = argV]
             /\ ret' = OK
        ELSE /\ store' = store
             /\ ret' = ERR
  /\ ready' = TRUE
  /\ op' = NoneOp
  /\ argK' = NoKey
  /\ argV' = NoVal

DeleteResp ==
  /\ ~ready /\ op = DeleteOp
  /\ IF store[argK] # MISSING
        THEN /\ store' = [store EXCEPT ![argK] = MISSING]
             /\ ret' = OK
        ELSE /\ store' = store
             /\ ret' = ERR
  /\ ready' = TRUE
  /\ op' = NoneOp
  /\ argK' = NoKey
  /\ argV' = NoVal

Request == GetReq \/ InsertReq \/ UpdateReq \/ DeleteReq
Response == GetResp \/ InsertResp \/ UpdateResp \/ DeleteResp

Next == Request \/ Response

vars == << store, op, argK, argV, ret, ready >>

Spec == Init /\ [][Next]_vars /\ WF_op(DeleteReq)

THEOREM Spec => []Inv

=============================================================================