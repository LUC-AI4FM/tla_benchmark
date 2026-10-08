---------------------------- MODULE Spec ----------------------------
EXTENDS Integers, TLC

CONSTANTS Keys, Vals, MISSING, NIL

VARIABLES op, args, ret, dict, state

TypeOK == 
  op \in {"get", "insert", "update", "delete", NIL} /\ 
  args \in (SUBSET (Keys \times Vals)) \cup {NIL} /\ 
  ret \in Vals \cup {"ok", "error", MISSING} /\ 
  dict \in [Keys -> Vals \cup {MISSING}] /\ 
  state \in {"ready", "working"}

Init == 
  op = NIL /\ 
  args = NIL /\ 
  ret = MISSING /\ 
  dict = [k \in Keys |-> MISSING] /\ 
  state = "ready"

RequestGet(k) == 
  op = "get" /\ 
  args = <<k>> /\ 
  state' = "working" /\ 
  UNCHANGED <<op, args, ret, dict>>

ResponseGet == 
  IF dict[args[1]] = MISSING THEN 
    ret' = MISSING 
  ELSE 
    ret' = dict[args[1]] 
  ENDIF /\ 
  op' = NIL /\ 
  args' = NIL /\ 
  state' = "ready" /\ 
  UNCHANGED <<dict>>

RequestInsert(k, v) == 
  op = "insert" /\ 
  args = <<k, v>> /\ 
  state' = "working" /\ 
  UNCHANGED <<op, args, ret, dict>>

ResponseInsert == 
  IF dict[args[1]] = MISSING THEN 
    dict' = [dict EXCEPT ![args[1]] = args[2]] /\ 
    ret' = "ok" 
  ELSE 
    dict' = dict /\ 
    ret' = "error" 
  ENDIF /\ 
  op' = NIL /\ 
  args' = NIL /\ 
  state' = "ready"

RequestUpdate(k, v) == 
  op = "update" /\ 
  args = <<k, v>> /\ 
  state' = "working" /\ 
  UNCHANGED <<op, args, ret, dict>>

ResponseUpdate == 
  IF dict[args[1]] /= MISSING THEN 
    dict' = [dict EXCEPT ![args[1]] = args[2]] /\ 
    ret' = "ok" 
  ELSE 
    dict' = dict /\ 
    ret' = "error" 
  ENDIF /\ 
  op' = NIL /\ 
  args' = NIL /\ 
  state' = "ready"

RequestDelete(k) == 
  op = "delete" /\ 
  args = <<k>> /\ 
  state' = "working" /\ 
  UNCHANGED <<op, args, ret, dict>>

ResponseDelete == 
  dict' = [x \in Keys |-> IF x = args[1] THEN MISSING ELSE dict[x]] /\ 
  ret' = "ok" /\ 
  op' = NIL /\ 
  args' = NIL /\ 
  state' = "ready"

Next == 
  (state = "ready") /\ 
    ((\E k \in Keys : RequestGet(k)) \/ 
     (\E k \in Keys, v \in Vals : RequestInsert(k, v)) \/ 
     (\E k \in Keys, v \in Vals : RequestUpdate(k, v)) \/ 
     (\E k \in Keys : RequestDelete(k))) 
  \/ 
  (state = "working") /\ 
    ((op = "get") /\ ResponseGet) \/ 
    ((op = "insert") /\ ResponseInsert) \/ 
    ((op = "update") /\ ResponseUpdate) \/ 
    ((op = "delete") /\ ResponseDelete)

Spec == Init /\ [][Next]_vars
====================================================================