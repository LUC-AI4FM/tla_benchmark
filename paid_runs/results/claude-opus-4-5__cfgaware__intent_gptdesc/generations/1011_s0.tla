---------------------------- MODULE KeyValueStore ----------------------------
CONSTANTS
    Keys,           \* Finite set of possible keys
    Values,         \* Finite set of possible values (excluding sentinel)
    Nil,            \* Sentinel value for "missing"
    Ok,             \* Result indicating success
    Error           \* Result indicating failure

VARIABLES
    store,          \* The abstract key-value mapping: Keys -> Values \cup {Nil}
    pending,        \* The pending request (or Nil if none)
    result          \* The result of the last completed operation (or Nil if none pending completion)

vars == <<store, pending, result>>

\* Operation types
OpGet == "get"
OpInsert == "insert"
OpUpdate == "update"
OpDelete == "delete"

\* Request record constructors
GetRequest(k) == [op |-> OpGet, key |-> k]
InsertRequest(k, v) == [op |-> OpInsert, key |-> k, value |-> v]
UpdateRequest(k, v) == [op |-> OpUpdate, key |-> k, value |-> v]
DeleteRequest(k) == [op |-> OpDelete, key |-> k]

\* Type invariant
TypeOK ==
    /\ store \in [Keys -> Values \cup {Nil}]
    /\ \/ pending = Nil
       \/ /\ pending.op = OpGet
          /\ pending.key \in Keys
       \/ /\ pending.op = OpInsert
          /\ pending.key \in Keys
          /\ pending.value \in Values
       \/ /\ pending.op = OpUpdate
          /\ pending.key \in Keys
          /\ pending.value \in Values
       \/ /\ pending.op = OpDelete
          /\ pending.key \in Keys
    /\ result \in Values \cup {Nil, Ok, Error}

\* Initial state: empty store, no pending request, no result
Init ==
    /\ store = [k \in Keys |-> Nil]
    /\ pending = Nil
    /\ result = Nil

\* Request transitions - begin an operation (only if no pending request)

RequestGet(k) ==
    /\ pending = Nil
    /\ pending' = GetRequest(k)
    /\ UNCHANGED <<store, result>>

RequestInsert(k, v) ==
    /\ pending = Nil
    /\ pending' = InsertRequest(k, v)
    /\ UNCHANGED <<store, result>>

RequestUpdate(k, v) ==
    /\ pending = Nil
    /\ pending' = UpdateRequest(k, v)
    /\ UNCHANGED <<store, result>>

RequestDelete(k) ==
    /\ pending = Nil
    /\ pending' = DeleteRequest(k)
    /\ UNCHANGED <<store, result>>

\* Response transitions - complete the pending operation

ResponseGet ==
    /\ pending # Nil
    /\ pending.op = OpGet
    /\ LET k == pending.key
       IN result' = store[k]  \* Returns value if present, Nil if absent
    /\ pending' = Nil
    /\ UNCHANGED store

ResponseInsert ==
    /\ pending # Nil
    /\ pending.op = OpInsert
    /\ LET k == pending.key
           v == pending.value
       IN IF store[k] = Nil
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = Ok
          ELSE /\ result' = Error
               /\ UNCHANGED store
    /\ pending' = Nil

ResponseUpdate ==
    /\ pending # Nil
    /\ pending.op = OpUpdate
    /\ LET k == pending.key
           v == pending.value
       IN IF store[k] # Nil
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = Ok
          ELSE /\ result' = Error
               /\ UNCHANGED store
    /\ pending' = Nil

ResponseDelete ==
    /\ pending # Nil
    /\ pending.op = OpDelete
    /\ LET k == pending.key
       IN /\ store' = [store EXCEPT ![k] = Nil]
          /\ result' = Ok
    /\ pending' = Nil

\* Combined actions
Request ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Values : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Values : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)

Response ==
    \/ ResponseGet
    \/ ResponseInsert
    \/ ResponseUpdate
    \/ ResponseDelete

Next == Request \/ Response

\* Fairness: every pending request eventually gets a response
Fairness == WF_vars(Response)

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* --------------------------------------------------------------------------
\* Safety Invariants
\* --------------------------------------------------------------------------

\* The store only contains valid values or Nil
StoreConsistency ==
    \A k \in Keys : store[k] \in Values \cup {Nil}

\* Results are always valid
ResultValidity ==
    result \in Values \cup {Nil, Ok, Error}

\* Combined safety invariant
SafetyInvariant == TypeOK /\ StoreConsistency /\ ResultValidity

\* --------------------------------------------------------------------------
\* Temporal Properties (Liveness)
\* --------------------------------------------------------------------------

\* Progress: any pending request eventually receives a response
Progress == pending # Nil ~> pending = Nil

\* Eventual service: the system can always accept new requests eventually
EventualService == []<>(pending = Nil)

\* --------------------------------------------------------------------------
\* Auxiliary predicates for verification
\* --------------------------------------------------------------------------

\* A key is present in the store
KeyPresent(k) == store[k] # Nil

\* A key is absent from the store
KeyAbsent(k) == store[k] = Nil

\* The store is empty
StoreEmpty == \A k \in Keys : store[k] = Nil

\* Count of present keys (for bounded model checking)
KeyCount == Cardinality({k \in Keys : KeyPresent(k)})

=============================================================================