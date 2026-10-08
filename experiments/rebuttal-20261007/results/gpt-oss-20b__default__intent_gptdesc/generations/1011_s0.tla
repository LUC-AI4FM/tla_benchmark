MODULE KeyValueStore
EXTENDS Sequences, TLC

CONSTANTS Keys, Values, Sentinel, OK, ERROR, Bottom

(* Type of an operation record *)
Op == [type : {"get","insert","update","delete"}, key : Keys, val : Values]

VARIABLES store, pendingStack, lastOp, lastResult

Init ==
  /\ store = [k \in Keys |-> Sentinel]
  /\ pendingStack = <<>>
  /\ lastOp = Bottom
  /\ lastResult = Sentinel

Request ==
  ∃ opType ∈ {"get","insert","update","delete"},
     k ∈ Keys,
     v ∈ Values :
    /\ pendingStack' = Append(pendingStack, [type |-> opType, key |-> k, val |-> v])
    /\ UNCHANGED <<store, lastOp, lastResult>>

Resp ==
  /\ Len(pendingStack) > 0
  /\ LET
        op == Head(pendingStack)
        k == op.key
        v == op.val
        oldVal == store[k]
        newStore ==
          IF op.type = "get" THEN store
          ELSEIF op.type = "insert" THEN
                IF oldVal = Sentinel THEN [store EXCEPT ![k] = v] ELSE store
          ELSEIF op.type = "update" THEN
                IF oldVal # Sentinel THEN [store EXCEPT ![k] = v] ELSE store
          ELSE (* delete *)
                [store EXCEPT ![k] = Sentinel]
        result ==
          IF op.type = "get" THEN oldVal
          ELSEIF op.type = "insert" THEN
                IF oldVal = Sentinel THEN OK ELSE ERROR
          ELSEIF op.type = "update" THEN
                IF oldVal # Sentinel THEN OK ELSE ERROR
          ELSE (* delete *)
                OK
      IN
        /\ store' = newStore
        /\ pendingStack' = Tail(pendingStack)
        /\ lastOp' = op
        /\ lastResult' = result

Next == Request \/ Resp

vars == <<store, pendingStack, lastOp, lastResult>>

StateConsistency ==
  ∀ k ∈ Keys : store[k] ∈ Values ∪ {Sentinel}

ReturnValueCorrectness ==
  /\ lastOp # Bottom
  /\ IF lastOp.type = "get" THEN lastResult = store[lastOp.key]
     ELSEIF lastOp.type = "insert" THEN
          IF lastResult = OK THEN store[lastOp.key] = lastOp.val
          ELSE lastResult = ERROR /\ store[lastOp.key] = Sentinel
     ELSEIF lastOp.type = "update" THEN
          IF lastResult = OK THEN store[lastOp.key] = lastOp.val
          ELSE lastResult = ERROR /\ store[lastOp.key] = Sentinel
     ELSE (* delete *)
          lastResult = OK /\ store[lastOp.key] = Sentinel

Spec == Init /\ [][Next]_vars /\ Fairness(Resp)

THEOREM StateConsistency_I := Spec => []StateConsistency
THEOREM ReturnValueCorrectness_I := Spec => []ReturnValueCorrectness