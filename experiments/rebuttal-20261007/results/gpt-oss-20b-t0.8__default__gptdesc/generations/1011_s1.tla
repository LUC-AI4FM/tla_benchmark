MODULE KeyValueStore
EXTENDS Sequences

CONSTANTS Keys, Values, MISSING, NULL

VARIABLES store, curOp, args, resp, ready, working

(* Type invariants *)
TypeInv ==
  /\ store \in [Keys -> (Values \cup {MISSING})]
  /\ curOp \in {"GET","INSERT","UPDATE","DELETE", "NONE"}
  /\ ready \in {TRUE, FALSE}
  /\ working \in {TRUE, FALSE}
  /\ resp \in (Values \cup {MISSING} \cup {NULL})
  /\ args \in Seq

(* Initial state *)
Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ curOp = "NONE"
  /\ args = << >>
  /\ resp = NULL
  /\ ready = TRUE
  /\ working = FALSE

(* Request actions *)
RequestGet(k) ==
  /\ ready
  /\ curOp = "NONE"
  /\ k \in Keys
  /\ store' = store
  /\ curOp' = "GET"
  /\ args' = <<k>>
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ resp' = NULL

RequestInsert(k,v) ==
  /\ ready
  /\ curOp = "NONE"
  /\ k \in Keys
  /\ v \in Values
  /\ store' = store
  /\ curOp' = "INSERT"
  /\ args' = <<k, v>>
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ resp' = NULL

RequestUpdate(k,v) ==
  /\ ready
  /\ curOp = "NONE"
  /\ k \in Keys
  /\ v \in Values
  /\ store[k] /= MISSING
  /\ store' = store
  /\ curOp' = "UPDATE"
  /\ args' = <<k, v>>
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ resp' = NULL

RequestDelete(k) ==
  /\ ready
  /\ curOp = "NONE"
  /\ k \in Keys
  /\ store' = store
  /\ curOp' = "DELETE"
  /\ args' = <<k>>
  /\ working' = TRUE
  /\ ready' = FALSE
  /\ resp' = NULL

(* Response actions *)
ResponseGet ==
  /\ working
  /\ curOp = "GET"
  /\ args[1] \in Keys
  /\ LET k == args[1]
     IN
       /\ store' = store
       /\ resp' = IF store[k] = MISSING THEN MISSING ELSE store[k]
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ curOp' = "NONE"
  /\ args' = << >>

ResponseInsert ==
  /\ working
  /\ curOp = "INSERT"
  /\ args[1] \in Keys
  /\ args[2] \in Values
  /\ LET k == args[1], v == args[2]
     IN
       /\ store' = IF store[k] = MISSING THEN [store EXCEPT ![k] = v] ELSE store
       /\ resp' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ curOp' = "NONE"
  /\ args' = << >>

ResponseUpdate ==
  /\ working
  /\ curOp = "UPDATE"
  /\ args[1] \in Keys
  /\ args[2] \in Values
  /\ LET k == args[1], v == args[2]
     IN
       /\ store' = IF store[k] /= MISSING THEN [store EXCEPT ![k] = v] ELSE store
       /\ resp' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ curOp' = "NONE"
  /\ args' = << >>

ResponseDelete ==
  /\ working
  /\ curOp = "DELETE"
  /\ args[1] \in Keys
  /\ LET k == args[1]
     IN
       /\ store' = IF store[k] /= MISSING THEN [store EXCEPT ![k] = MISSING] ELSE store
       /\ resp' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ curOp' = "NONE"
  /\ args' = << >>

Next ==
  \/ (∃ k \in Keys : RequestGet(k))
  \/ (∃ k \in Keys, v \in Values : RequestInsert(k,v))
  \/ (∃ k \in Keys, v \in Values : RequestUpdate(k,v))
  \/ (∃ k \in Keys : RequestDelete(k))
  \/ ResponseGet
  \/ ResponseInsert
  \/ ResponseUpdate
  \/ ResponseDelete

Spec ==
  Init /\ [][Next]_vars /\ WF_vars[ResponseDelete] /\ TypeInv

=============================================================================
