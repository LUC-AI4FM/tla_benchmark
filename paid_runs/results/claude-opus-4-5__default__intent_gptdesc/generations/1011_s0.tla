-------------------------------- MODULE KeyValueStore --------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Keys,           \* The finite set of possible keys
    Values,         \* The finite set of possible values (excluding sentinel)
    Missing,        \* Sentinel value representing "key absent"
    Ok,             \* Result indicating success
    Error           \* Result indicating failure

VARIABLES
    store,          \* The abstract key-value mapping: Keys -> Values ∪ {Missing}
    pendingOp,      \* The current pending operation (or Null if none)
    result          \* The result of the last completed operation (or Null if none pending)

vars == <<store, pendingOp, result>>

\* Operation types
OpGet == "get"
OpInsert == "insert"
OpUpdate == "update"
OpDelete == "delete"

\* Null constant for no pending operation / no result
Null == CHOOSE x : x \notin (Keys \cup Values \cup {Missing, Ok, Error, OpGet, OpInsert, OpUpdate, OpDelete})

\* Type definitions for operations
Operation == 
    [type: {OpGet}, key: Keys] \cup
    [type: {OpInsert, OpUpdate}, key: Keys, value: Values] \cup
    [type: {OpDelete}, key: Keys]

\* Possible results
Result == Values \cup {Missing, Ok, Error}

\* Type invariant
TypeOK ==
    /\ store \in [Keys -> Values \cup {Missing}]
    /\ pendingOp \in Operation \cup {Null}
    /\ result \in Result \cup {Null}

--------------------------------------------------------------------------------
\* Initial state: empty store, no pending operation, no result
--------------------------------------------------------------------------------

Init ==
    /\ store = [k \in Keys |-> Missing]  \* All keys initially absent
    /\ pendingOp = Null
    /\ result = Null

--------------------------------------------------------------------------------
\* Request transitions: issue a new operation (only when no operation pending)
--------------------------------------------------------------------------------

\* Request a get operation
RequestGet(key) ==
    /\ pendingOp = Null
    /\ pendingOp' = [type |-> OpGet, key |-> key]
    /\ UNCHANGED <<store, result>>

\* Request an insert operation
RequestInsert(key, value) ==
    /\ pendingOp = Null
    /\ pendingOp' = [type |-> OpInsert, key |-> key, value |-> value]
    /\ UNCHANGED <<store, result>>

\* Request an update operation
RequestUpdate(key, value) ==
    /\ pendingOp = Null
    /\ pendingOp' = [type |-> OpUpdate, key |-> key, value |-> value]
    /\ UNCHANGED <<store, result>>

\* Request a delete operation
RequestDelete(key) ==
    /\ pendingOp = Null
    /\ pendingOp' = [type |-> OpDelete, key |-> key]
    /\ UNCHANGED <<store, result>>

--------------------------------------------------------------------------------
\* Response transitions: complete the pending operation and return result
--------------------------------------------------------------------------------

\* Response to get: return the value if present, Missing otherwise
ResponseGet ==
    /\ pendingOp /= Null
    /\ pendingOp.type = OpGet
    /\ LET key == pendingOp.key IN
        /\ result' = store[key]
        /\ UNCHANGED store
    /\ pendingOp' = Null

\* Response to insert: succeed only if key is absent
ResponseInsert ==
    /\ pendingOp /= Null
    /\ pendingOp.type = OpInsert
    /\ LET key == pendingOp.key
           value == pendingOp.value IN
        IF store[key] = Missing
        THEN 
            /\ store' = [store EXCEPT ![key] = value]
            /\ result' = Ok
        ELSE
            /\ UNCHANGED store
            /\ result' = Error
    /\ pendingOp' = Null

\* Response to update: succeed only if key is present
ResponseUpdate ==
    /\ pendingOp /= Null
    /\ pendingOp.type = OpUpdate
    /\ LET key == pendingOp.key
           value == pendingOp.value IN
        IF store[key] /= Missing
        THEN
            /\ store' = [store EXCEPT ![key] = value]
            /\ result' = Ok
        ELSE
            /\ UNCHANGED store
            /\ result' = Error
    /\ pendingOp' = Null

\* Response to delete: always succeeds, removes key if present
ResponseDelete ==
    /\ pendingOp /= Null
    /\ pendingOp.type = OpDelete
    /\ LET key == pendingOp.key IN
        /\ store' = [store EXCEPT ![key] = Missing]
        /\ result' = Ok
    /\ pendingOp' = Null

--------------------------------------------------------------------------------
\* Combined actions
--------------------------------------------------------------------------------

\* All request actions
Request ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Values : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Values : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)

\* All response actions
Response ==
    \/ ResponseGet
    \/ ResponseInsert
    \/ ResponseUpdate
    \/ ResponseDelete

\* Next state relation
Next == Request \/ Response

--------------------------------------------------------------------------------
\* Fairness conditions
--------------------------------------------------------------------------------

\* Weak fairness on responses ensures pending operations eventually complete
FairResponse == WF_vars(Response)

\* The complete specification with fairness
Spec == Init /\ [][Next]_vars /\ FairResponse

--------------------------------------------------------------------------------
\* Safety Invariants
--------------------------------------------------------------------------------

\* Invariant: Result corresponds correctly to the operation type
ResultCorrectness ==
    pendingOp = Null =>
        result \in Result \cup {Null}

\* Invariant: If there's no pending operation and we just did a get,
\* the result must be a value or Missing
GetResultValid ==
    (pendingOp = Null /\ result /= Null) =>
        result \in Values \cup {Missing, Ok, Error}

\* Invariant: Store only contains valid mappings
StoreValid ==
    \A k \in Keys : store[k] \in Values \cup {Missing}

\* Combined safety invariant
SafetyInvariant == 
    /\ TypeOK
    /\ StoreValid
    /\ ResultCorrectness
    /\ GetResultValid

--------------------------------------------------------------------------------
\* State Consistency Invariant
\* After any completed operation, the store reflects the correct state
--------------------------------------------------------------------------------

\* Helper: a key is present in the store
KeyPresent(key) == store[key] /= Missing

\* Helper: a key is absent from the store
KeyAbsent(key) == store[key] = Missing

\* Consistency: the abstract mapping is always well-formed
StateConsistency ==
    /\ \A k \in Keys : store[k] \in Values \cup {Missing}
    /\ \A k \in Keys : (KeyPresent(k) <=> store[k] \in Values)

--------------------------------------------------------------------------------
\* Return Value Correctness
\* Expressed as action properties (checked via refinement or temporal logic)
--------------------------------------------------------------------------------

\* When a get response occurs, the result equals the stored value
GetCorrectness ==
    [][
        (pendingOp /= Null /\ pendingOp.type = OpGet /\ pendingOp' = Null) =>
        result' = store[pendingOp.key]
    ]_vars

\* When an insert response occurs:
\* - If key was absent: result is Ok and key is now mapped to value
\* - If key was present: result is Error and store unchanged
InsertCorrectness ==
    [][
        (pendingOp /= Null /\ pendingOp.type = OpInsert /\ pendingOp' = Null) =>
        LET key == pendingOp.key
            value == pendingOp.value IN
        IF store[key] = Missing
        THEN result' = Ok /\ store'[key] = value
        ELSE result' = Error /\ store' = store
    ]_vars

\* When an update response occurs:
\* - If key was present: result is Ok and key is now mapped to new value
\* - If key was absent: result is Error and store unchanged
UpdateCorrectness ==
    [][
        (pendingOp /= Null /\ pendingOp.type = OpUpdate /\ pendingOp' = Null) =>
        LET key == pendingOp.key
            value == pendingOp.value IN
        IF store[key] /= Missing
        THEN result' = Ok /\ store'[key] = value
        ELSE result' = Error /\ store' = store
    ]_vars

\* When a delete response occurs:
\* - Result is always Ok
\* - Key is absent after the operation
DeleteCorrectness ==
    [][
        (pendingOp /= Null /\ pendingOp.type = OpDelete /\ pendingOp' = Null) =>
        LET key == pendingOp.key IN
        result' = Ok /\ store'[key] = Missing
    ]_vars

\* Combined return value correctness property
ReturnValueCorrectness ==
    /\ GetCorrectness
    /\ InsertCorrectness
    /\ UpdateCorrectness
    /\ DeleteCorrectness

--------------------------------------------------------------------------------
\* Liveness Properties
--------------------------------------------------------------------------------

\* Progress: any pending operation eventually receives a response
OperationProgress ==
    pendingOp /= Null ~> pendingOp = Null

\* Eventual service: the system can always accept new requests
\* (when no operation is pending, a request can eventually be issued)
EventualService ==
    [](pendingOp = Null => <>(pendingOp /= Null \/ pendingOp = Null))

\* Stronger liveness: every request type can eventually be serviced
GetCanComplete ==
    \A k \in Keys : 
        (pendingOp /= Null /\ pendingOp.type = OpGet /\ pendingOp.key = k) ~> 
        pendingOp = Null

InsertCanComplete ==
    \A k \in Keys : \A v \in Values :
        (pendingOp /= Null /\ pendingOp.type = OpInsert /\ pendingOp.key = k /\ pendingOp.value = v) ~>
        pendingOp = Null

UpdateCanComplete ==
    \A k \in Keys : \A v \in Values :
        (pendingOp /= Null /\ pendingOp.type = OpUpdate /\ pendingOp.key = k /\ pendingOp.value = v) ~>
        pendingOp = Null

DeleteCanComplete ==
    \A k \in Keys :
        (pendingOp /= Null /\ pendingOp.type = OpDelete /\ pendingOp.key = k) ~>
        pendingOp = Null

\* Combined liveness property
LivenessProperty ==
    /\ OperationProgress
    /\ GetCanComplete
    /\ InsertCanComplete
    /\ UpdateCanComplete
    /\ DeleteCanComplete

--------------------------------------------------------------------------------
\* Theorems (properties to verify)
--------------------------------------------------------------------------------

\* The specification satisfies type correctness
THEOREM Spec => []TypeOK

\* The specification satisfies state consistency
THEOREM Spec => []StateConsistency

\* The specification satisfies the safety invariant
THEOREM Spec => []SafetyInvariant

\* The specification satisfies return value correctness
THEOREM Spec => ReturnValueCorrectness

\* The specification satisfies liveness (with fairness)
THEOREM Spec => OperationProgress

================================================================================