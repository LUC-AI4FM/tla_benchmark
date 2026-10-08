----------------------------- MODULE KeyValueStore -----------------------------

EXTENDS TLC

CONSTANTS
    KEYS, VALUES,
    None, NoKey, NoVal, NoOp, NoResp,
    MISSING, OK, ERROR

ASSUME
    /\ NoKey \notin KEYS
    /\ NoVal \notin VALUES
    /\ None \notin VALUES
    /\ MISSING \notin VALUES
    /\ OK \notin VALUES
    /\ ERROR \notin VALUES

VARIABLES
    kv,        \* store: total map KEYS -> VALUES ∪ {None}; None denotes absence
    op,        \* current operation: one of Ops or NoOp when idle
    key,       \* current key argument: in KEYS when a request is active, NoKey when idle
    val,       \* current value argument: in VALUES for insert/update, NoVal otherwise
    resp,      \* response value: in RetVal when processed, NoResp otherwise
    status     \* protocol phase: "Idle", "Requested", "Processed"

Ops == {"get", "insert", "update", "delete"}
ValueOpt == VALUES \cup {None}
RetGet == VALUES \cup {MISSING}
RetWrite == {OK, ERROR}
RetVal == RetGet \cup RetWrite

vars == << kv, op, key, val, resp, status >>

Init ==
    /\ kv \in [KEYS -> ValueOpt]
    /\ \A k \in KEYS: kv[k] = None
    /\ op = NoOp
    /\ key = NoKey
    /\ val = NoVal
    /\ resp = NoResp
    /\ status = "Idle"

Submit ==
    /\ status = "Idle"
    /\ op' \in Ops
    /\ key' \in KEYS
    /\ resp' = NoResp
    /\ status' = "Requested"
    /\ IF op' \in {"insert","update"} THEN val' \in VALUES ELSE val' = NoVal
    /\ UNCHANGED kv

ProcessGet ==
    /\ status = "Requested"
    /\ op = "get"
    /\ resp' = IF kv[key] = None THEN MISSING ELSE kv[key]
    /\ status' = "Processed"
    /\ UNCHANGED << kv, op, key, val >>

ProcessInsert ==
    /\ status = "Requested"
    /\ op = "insert"
    /\ IF kv[key] = None
          THEN /\ kv' = [kv EXCEPT ![key] = val]
               /\ resp' = OK
          ELSE /\ UNCHANGED kv
               /\ resp' = ERROR
    /\ status' = "Processed"
    /\ UNCHANGED << op, key, val >>

ProcessUpdate ==
    /\ status = "Requested"
    /\ op = "update"
    /\ IF kv[key] # None
          THEN /\ kv' = [kv EXCEPT ![key] = val]
               /\ resp' = OK
          ELSE /\ UNCHANGED kv
               /\ resp' = ERROR
    /\ status' = "Processed"
    /\ UNCHANGED << op, key, val >>

ProcessDelete ==
    /\ status = "Requested"
    /\ op = "delete"
    /\ kv' = [kv EXCEPT ![key] = None]
    /\ resp' = OK
    /\ status' = "Processed"
    /\ UNCHANGED << op, key, val >>

Respond ==
    /\ status = "Processed"
    /\ status' = "Idle"
    /\ op' = NoOp
    /\ key' = NoKey
    /\ val' = NoVal
    /\ resp' = NoResp
    /\ UNCHANGED kv

Next ==
    \/ Submit
    \/ ProcessGet
    \/ ProcessInsert
    \/ ProcessUpdate
    \/ ProcessDelete
    \/ Respond

\* Type-correctness (safety) invariant
TypeInv ==
    /\ kv \in [KEYS -> ValueOpt]
    /\ op \in Ops \cup {NoOp}
    /\ key \in KEYS \cup {NoKey}
    /\ val \in VALUES \cup {NoVal}
    /\ resp \in RetVal \cup {NoResp}
    /\ status \in {"Idle","Requested","Processed"}
    /\ (status = "Idle") =>
         /\ op = NoOp
         /\ key = NoKey
         /\ val = NoVal
         /\ resp = NoResp
    /\ (status = "Requested") =>
         /\ op \in Ops
         /\ key \in KEYS
         /\ resp = NoResp
         /\ IF op \in {"insert","update"} THEN val \in VALUES ELSE val = NoVal
    /\ (status = "Processed") =>
         /\ op \in Ops
         /\ key \in KEYS
         /\ IF op = "get"
               THEN resp \in RetGet
               ELSE IF op \in {"insert","update"}
                       THEN resp \in RetWrite
                       ELSE /\ op = "delete" /\ resp = OK

\* Fair progress for delete requests: when a delete request is pending, it is eventually processed and responded.
RespondDelete == Respond /\ op = "delete"

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProcessDelete)
    /\ WF_vars(RespondDelete)

=============================================================================