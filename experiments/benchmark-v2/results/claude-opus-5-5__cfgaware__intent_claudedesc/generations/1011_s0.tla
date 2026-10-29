---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, TLC

CONSTANTS Keys, Vals, NIL, MISSING

ASSUME NIL \notin Vals /\ MISSING \notin Vals /\ NIL # MISSING

VARIABLES store, op, args, ret, state

vars == <<store, op, args, ret, state>>

Ops == {"get", "insert", "update", "delete"}

States == {"ready", "pending", "done"}

RetVals == Vals \cup {NIL, MISSING, "ok", "error"}

ArgVals == [key : Keys \cup {NIL}, val : Vals \cup {NIL}]

NoArgs == [key |-> NIL, val |-> NIL]

TypeOK ==
    /\ store \in [Keys -> Vals \cup {NIL}]
    /\ op \in Ops \cup {NIL}
    /\ args \in ArgVals
    /\ ret \in RetVals
    /\ state \in States

Init ==
    /\ store = [k \in Keys |-> NIL]
    /\ op = NIL
    /\ args = NoArgs
    /\ ret = NIL
    /\ state = "ready"

Present(k) == store[k] # NIL

\* ---------------- Request phase: client submits a request ----------------

RequestGet(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> NIL]
    /\ ret' = NIL
    /\ state' = "pending"
    /\ UNCHANGED store

RequestInsert(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = NIL
    /\ state' = "pending"
    /\ UNCHANGED store

RequestUpdate(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = NIL
    /\ state' = "pending"
    /\ UNCHANGED store

RequestDelete(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> NIL]
    /\ ret' = NIL
    /\ state' = "pending"
    /\ UNCHANGED store

Request ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Vals : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Vals : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)

\* ---------------- Processing phase: the store handles the request ----------------

DoGet ==
    /\ state = "pending"
    /\ op = "get"
    /\ ret' = IF Present(args.key) THEN store[args.key] ELSE MISSING
    /\ state' = "done"
    /\ UNCHANGED <<store, op, args>>

DoInsert ==
    /\ state = "pending"
    /\ op = "insert"
    /\ IF Present(args.key)
          THEN /\ ret' = "error"
               /\ UNCHANGED store
          ELSE /\ store' = [store EXCEPT ![args.key] = args.val]
               /\ ret' = "ok"
    /\ state' = "done"
    /\ UNCHANGED <<op, args>>

DoUpdate ==
    /\ state = "pending"
    /\ op = "update"
    /\ IF Present(args.key)
          THEN /\ store' = [store EXCEPT ![args.key] = args.val]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED store
    /\ state' = "done"
    /\ UNCHANGED <<op, args>>

DoDelete ==
    /\ state = "pending"
    /\ op = "delete"
    /\ store' = [store EXCEPT ![args.key] = NIL]
    /\ ret' = "ok"
    /\ state' = "done"
    /\ UNCHANGED <<op, args>>

Process == DoGet \/ DoInsert \/ DoUpdate \/ DoDelete

\* ---------------- Response phase: the result is returned to the client ----------------

Respond ==
    /\ state = "done"
    /\ op' = NIL
    /\ args' = NoArgs
    /\ state' = "ready"
    /\ UNCHANGED <<store, ret>>

RespondDelete ==
    /\ op = "delete"
    /\ Respond

Next == Request \/ Process \/ Respond

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(DoDelete)
    /\ WF_vars(RespondDelete)

\* ---------------- Properties ----------------

DeleteCompletes ==
    (state = "pending" /\ op = "delete") ~> (state = "ready")

THEOREM Spec => []TypeOK
=============================================================================