---------------- MODULE KeyValueStore ----------------

EXTENDS Integers, FiniteSets

CONSTANTS Keys, Vals, MISSING, SUCCESS, FAILURE, Nil

ASSUME Nil \notin (Keys \cup Vals \cup {MISSING, SUCCESS, FAILURE})
ASSUME MISSING \notin Vals
ASSUME SUCCESS \notin Vals
ASSUME FAILURE \notin Vals
ASSUME SUCCESS # FAILURE

VARIABLES store, state, op, arg1, arg2, ret

vars == <<store, state, op, arg1, arg2, ret>>

\* The set of possible operations the system can be performing.
Operations == {"get", "insert", "update", "delete", "idle"}

\* The two main states of the system: ready for a new request or working on one.
SystemState == {"ready", "working"}

\* -- Initialization --

Init ==
    /\ store = [k \in Keys |-> MISSING]
    /\ state = "ready"
    /\ op = "idle"
    /\ arg1 = Nil
    /\ arg2 = Nil
    /\ ret = Nil

\* -- Actions --

\* A client requests to get the value for key k.
RequestGet(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "get"
    /\ arg1' = k
    /\ UNCHANGED <<store, arg2, ret>>

\* A client requests to insert a value v for key k.
RequestInsert(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "insert"
    /\ arg1' = k
    /\ arg2' = v
    /\ UNCHANGED <<store, ret>>

\* A client requests to update the value to v for key k.
RequestUpdate(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "update"
    /\ arg1' = k
    /\ arg2' = v
    /\ UNCHANGED <<store, ret>>

\* A client requests to delete the entry for key k.
RequestDelete(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "delete"
    /\ arg1' = k
    /\ UNCHANGED <<store, arg2, ret>>

\* The system processes the pending "get" request.
RespondGet ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = store[arg1]
    /\ state' = "ready"
    /\ op' = "idle"
    /\ UNCHANGED <<store, arg1, arg2>>

\* The system processes the pending "insert" request.
\* Succeeds if the key does not exist, fails otherwise.
RespondInsert ==
    /\ state = "working"
    /\ op = "insert"
    /\ IF store[arg1] = MISSING
       THEN /\ store' = [store EXCEPT ![arg1] = arg2]
            /\ ret' = SUCCESS
       ELSE /\ store' = store
            /\ ret' = FAILURE
    /\ state' = "ready"
    /\ op' = "idle"
    /\ UNCHANGED <<arg1, arg2>>

\* The system processes the pending "update" request.
\* Succeeds if the key exists, fails otherwise.
RespondUpdate ==
    /\ state = "working"
    /\ op = "update"
    /\ IF store[arg1] # MISSING
       THEN /\ store' = [store EXCEPT ![arg1] = arg2]
            /\ ret' = SUCCESS
       ELSE /\ store' = store
            /\ ret' = FAILURE
    /\ state' = "ready"
    /\ op' = "idle"
    /\ UNCHANGED <<arg1, arg2>>

\* The system processes the pending "delete" request.
\* Succeeds if the key exists, fails otherwise.
RespondDelete ==
    /\ state = "working"
    /\ op = "delete"
    /\ IF store[arg1] # MISSING
       THEN /\ store' = [store EXCEPT ![arg1] = MISSING]
            /\ ret' = SUCCESS
       ELSE /\ store' = store
            /\ ret' = FAILURE
    /\ state' = "ready"
    /\ op' = "idle"
    /\ UNCHANGED <<arg1, arg2>>

\* The next-state relation.
Next ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Vals : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Vals : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)
    \/ RespondGet
    \/ RespondInsert
    \/ RespondUpdate
    \/ RespondDelete

\* -- Specification --

Spec == Init /\ [][Next]_vars /\ WF_vars(RespondDelete)

=============================================================================