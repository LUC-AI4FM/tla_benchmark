MODULE KVStore
EXTENDS Naturals, Sequences

CONSTANTS KeySet, ValSet, Nil

(* Variables *)
VARIABLE store, pending, nextReqId, resp

(* Initial state *)
Init ==
  /\ store = [k \in KeySet |-> Nil]
  /\ pending = << >>
  /\ nextReqId = 0
  /\ resp = [ ]

(* Request action *)
Request(op, key, val) ==
  /\ op \in {"get","insert","update","delete"}
  /\ key \in KeySet
  /\ (op = "get" \/ op = "delete") => val = Nil
  /\ (op = "insert" \/ op = "update") => val \in ValSet
  /\ pending' = Append(pending, [id |-> nextReqId, op |-> op, key |-> key, val |-> val])
  /\ nextReqId' = nextReqId + 1
  /\ UNCHANGED store
  /\ UNCHANGED resp

(* Response actions *)
GetResponse ==
  /\ Len(pending) > 0
  /\ LET r == Last(pending) IN
     /\ r.op = "get"
     /\ pending' = pending[1 .. Len(pending)-1]
     /\ UNCHANGED nextReqId
     /\ resp' = [resp EXCEPT ![r.id] = store[r.key]]
     /\ UNCHANGED store

InsertResponse ==
  /\ Len(pending) > 0
  /\ LET r == Last(pending) IN
     /\ r.op = "insert"
     /\ pending' = pending[1 .. Len(pending)-1]
     /\ UNCHANGED nextReqId
     /\ IF store[r.key] = Nil THEN
          store' = [store EXCEPT ![r.key] = r.val];
          resp' = [resp EXCEPT ![r.id] = "ok"]
        ELSE
          store' = store;
          resp' = [resp EXCEPT ![r.id] = "error"]

UpdateResponse ==
  /\ Len(pending) > 0
  /\ LET r == Last(pending) IN
     /\ r.op = "update"
     /\ pending' = pending[1 .. Len(pending)-1]
     /\ UNCHANGED nextReqId
     /\ IF store[r.key] # Nil THEN
          store' = [store EXCEPT ![r.key] = r.val];
          resp' = [resp EXCEPT ![r.id] = "ok"]
        ELSE
          store' = store;
          resp' = [resp EXCEPT ![r.id] = "error"]

DeleteResponse ==
  /\ Len(pending) > 0
  /\ LET r == Last(pending) IN
     /\ r.op = "delete"
     /\ pending' = pending[1 .. Len(pending)-1]
     /\ UNCHANGED nextReqId
     /\ store' = [store EXCEPT ![r.key] = Nil];
     /\ resp' = [resp EXCEPT ![r.id] = "ok"]

(* Next action *)
Next ==
  ∃op \in {"get","insert","update","delete"}, key \in KeySet, val \in ValSet \cup {Nil} :
      Request(op,key,val)
  \/ GetResponse
  \/ InsertResponse
  \/ UpdateResponse
  \/ DeleteResponse

vars == << store, pending, nextReqId, resp >>

(* Type invariants *)
StoreType ==
  store ∈ [KeySet -> ValSet \cup {Nil}]
PendingType ==
  pending ∈ Seq([id : Nat, op : {"get","insert","update","delete"}, key : KeySet, val : ValSet \cup {Nil}])
NextReqIdNonNegative == nextReqId ∈ Nat
RespType == resp ∈ [Nat -> ValSet \cup {Nil} \cup {"ok","error"}]

SafetyInvariant ==
  StoreType /\ PendingType /\ NextReqIdNonNegative /\ RespType

Spec == Init /\ [][Next]_vars

ResponseActions == GetResponse \/ InsertResponse \/ UpdateResponse \/ DeleteResponse
Liveness == WF_1(ResponseActions)

=============================================================================
