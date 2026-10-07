```
MODULE KeyValueStore
EXTENDS Integers, TLC

CONSTANTS Keys, Vals, MISSING, NIL

VARIABLES op, args, ret, dict, state

Init ==
  /\ op = NIL
  /\ args = NIL
  /\ ret = NIL
  /\ dict = [k \in Keys |-> MISSING]
  /\ state = "ready"

TypeOK ==
  /\ op \in {"get", "insert", "update", "delete", NIL}
  /\ args \in {[k \in Keys |-> Vals] \cup [k \in Keys |-> {NIL}] \cup {NIL}}
  /\ ret \in (Vals \cup {"ok", "error", MISSING, NIL})
  /\ dict = [k \in Keys |-> Vals \cup {MISSING}]
  /\ state \in {"ready", "working"}

RequestGet ==
  /\ state = "ready"
  /\ op' = "get"
  /\ args' = <<args.key>>
  /\ ret' = NIL
  /\ dict' = dict
  /\ state' = "working"

ResponseGet ==
  /\ state = "working"
  /\ op = "get"
  /\ args = <<args.key>>
  /\ ret' = IF dict[args.key] = MISSING THEN MISSING ELSE dict[args.key]
  /\ dict' = dict
  /\ state' = "ready"

RequestInsert ==
  /\ state = "ready"
  /\ op' = "insert"
  /\ args' = <<args.key, args.val>>
  /\ ret' = NIL
  /\ dict' = dict
  /\ state' = "working"

ResponseInsert ==
  /\ state = "working"
  /\ op = "insert"
  /\ args = <<args.key, args.val>>
  /\ IF dict[args.key] = MISSING
    THEN
      /\ dict' = [dict EXCEPT ![args.key] = args.val]
      /\ ret' = "ok"
    ELSE
      /\ dict' = dict
      /\ ret' = "error"
  /\ state' = "ready"

RequestUpdate ==
  /\ state = "ready"
  /\ op' = "update"
  /\ args' = <<args.key, args.val>>
  /\ ret' = NIL
  /\ dict' = dict
  /\ state' = "working"

ResponseUpdate ==
  /\ state = "working"
  /\ op = "update"
  /\ args = <<args.key, args.val>>
  /\ IF dict[args.key] /= MISSING
    THEN
      /\ dict' = [dict EXCEPT ![args.key] = args.val]
      /\ ret' = "ok"
    ELSE
      /\ dict' = dict
      /\ ret' = "error"
  /\ state' = "ready"

RequestDelete ==
  /\ state = "ready"
  /\ op' = "delete"
  /\ args' = <<args.key>>
  /\ ret' = NIL
  /\ dict' = dict
  /\ state' = "working"

ResponseDelete ==
  /\ state = "working"
  /\ op = "delete"
  /\ args = <<args.key>>
  /\ dict' = [dict EXCEPT ![args.key] = MISSING]
  /\ ret' = "ok"
  /\ state' = "ready"

Next ==
  \/ RequestGet
  \/ ResponseGet
  \/ RequestInsert
  \/ ResponseInsert
  \/ RequestUpdate
  \/ ResponseUpdate
  \/ RequestDelete
  \/ ResponseDelete

Spec == Init /\ [][Next]_vars
WF_Delete == WF_vars(RequestDelete)

THEOREM Spec => []TypeOK
THEOREM Spec => WF_Delete
```