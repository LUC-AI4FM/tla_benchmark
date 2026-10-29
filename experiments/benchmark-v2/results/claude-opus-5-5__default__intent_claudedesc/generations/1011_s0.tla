---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Vals

ASSUME Keys # {} /\ Vals # {}

NoVal == CHOOSE v : v \notin Vals

Ops       == {"get", "insert", "update", "delete"}
NoArg     == "none"
RetVals   == Vals \cup {"ok", "error", "missing", "none"}
States    == {"ready", "busy"}

VARIABLES store, op, args, ret, state

vars == <<store, op, args, ret, state>>

TypeOK ==
    /\ store \in [Keys -> Vals \cup {NoVal}]
    /\ op \in Ops \cup {"none"}
    /\ args \in [key : Keys \cup {NoArg}, val : Vals \cup {NoArg}]
    /\ ret \in RetVals
    /\ state \in States

Init ==
    /\ store = [k \in Keys |-> NoVal]
    /\ op = "none"
    /\ args = [key |-> NoArg, val |-> NoArg]
    /\ ret = "none"
    /\ state = "ready"

----------------------------------------------------------------------------
(* Phase 1: client submits a request *)

RequestGet(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> NoArg]
    /\ ret' = "none"
    /\ state' = "busy"
    /\ UNCHANGED store

RequestInsert(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = "none"
    /\ state' = "busy"
    /\ UNCHANGED store

RequestUpdate(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = "none"
    /\ state' = "busy"
    /\ UNCHANGED store

RequestDelete(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> NoArg]
    /\ ret' = "none"
    /\ state' = "busy"
    /\ UNCHANGED store

----------------------------------------------------------------------------
(* Phase 2: store processes the request and returns a result *)

ProcessGet ==
    /\ state = "busy"
    /\ op = "get"
    /\ ret' = IF store[args.key] = NoVal THEN "missing" ELSE store[args.key]
    /\ state' = "ready"
    /\ UNCHANGED <<store, op, args>>

ProcessInsert ==
    /\ state = "busy"
    /\ op = "insert"
    /\ IF store[args.key] = NoVal
          THEN /\ store' = [store EXCEPT ![args.key] = args.val]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED store
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

ProcessUpdate ==
    /\ state = "busy"
    /\ op = "update"
    /\ IF store[args.key] # NoVal
          THEN /\ store' = [store EXCEPT ![args.key] = args.val]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED store
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

ProcessDelete ==
    /\ state = "busy"
    /\ op = "delete"
    /\ store' = [store EXCEPT ![args.key] = NoVal]
    /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

----------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Vals : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Vals : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)
    \/ ProcessGet
    \/ ProcessInsert
    \/ ProcessUpdate
    \/ ProcessDelete

Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessDelete)

----------------------------------------------------------------------------
(* Properties *)

THEOREM Spec => []TypeOK

\* Every pending delete request is eventually processed with result "ok".
DeleteProgress ==
    (state = "busy" /\ op = "delete") ~> (state = "ready" /\ ret = "ok")

THEOREM Spec => DeleteProgress
=============================================================================