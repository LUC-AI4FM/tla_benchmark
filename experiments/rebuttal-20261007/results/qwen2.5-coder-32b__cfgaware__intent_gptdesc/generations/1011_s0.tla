------------------------------- MODULE KeyValueStore -------------------------------

CONSTANTS Keys, Values, Sentinel

VARIABLES store, requests, responses

(* --algorithm KeyValueStore

variables 
    store = [k \in Keys |-> Sentinel],  \* Initial state with all keys mapped to Sentinel
    requests = <<>>,                      \* Queue of pending requests
    responses = <<>>;                     \* Queue of generated responses

\* Define the possible operations
Get(key) == << "get", key >>
Insert(key, value) == << "insert", key, value >>
Update(key, value) == << "update", key, value >>
Delete(key) == << "delete", key >>

\* Process a request and generate a response
ProcessRequest(request) ==
    LET op == request[1]
        key == request[2]
        value == IF op \in {"insert", "update"} THEN request[3] ELSE Sentinel
    IN
        CASE op = "get" ->
            <<request, IF store[key] = Sentinel THEN Sentinel ELSE store[key]>>
        [] op = "insert" ->
            IF store[key] = Sentinel THEN
                <<request, "ok">>
            ELSE
                <<request, "error">>
            ENDIF
        [] op = "update" ->
            IF store[key] \= Sentinel THEN
                <<request, "ok">>
            ELSE
                <<request, "error">>
            ENDIF
        [] op = "delete" ->
            <<request, "ok">>

\* Update the store based on a request and response pair
UpdateStore(request, response) ==
    LET op == request[1]
        key == request[2]
        value == IF op \in {"insert", "update"} THEN request[3] ELSE Sentinel
    IN
        CASE op = "get" -> store
        [] op = "insert" /\ response = "ok" -> [store EXCEPT ![key] = value]
        [] op = "update" /\ response = "ok" -> [store EXCEPT ![key] = value]
        [] op = "delete" /\ response = "ok" -> [store EXCEPT ![key] = Sentinel]
        [] OTHER -> store

\* Initial predicate
Init ==
    /\ store \in [Keys -> Values \/ {Sentinel}]
    /\ requests = <<>>
    /\ responses = <<>>

\* Next-state relation
Next ==
    \/ /\ requests # <<>> 
       /\ LET request == Head(requests)
              response == ProcessRequest(request)
          IN
             /\ requests' = Tail(requests) 
             /\ responses' = Append(responses, response)
             /\ store' = UpdateStore(request, response[2])
    \/ /\ requests = <<>>
       /\ responses # <<>>
       /\ \E request \in DOMAIN requests : 
            LET response == Head(responses)
                newStore == UpdateStore(request, response[2])
            IN
               /\ requests' = [requests EXCEPT ![request] =<< >>]
               /\ responses' = Tail(responses)
               /\ store' = newStore

\* Specification
Spec ==
    Init /\ [][Next]_<<store, requests, responses>>

\* Invariants
StateConsistency ==
    \A key \in Keys : 
        \/ store[key] = Sentinel
        \/ \E request \in DOMAIN requests :
            LET op == request[1]
                reqKey == request[2]
                value == IF op \in {"insert", "update"} THEN request[3] ELSE Sentinel
            IN
               op = "get" /\ store[key] = Sentinel
               \/ op = "insert" /\ key = reqKey /\ store[key] = value
               \/ op = "update" /\ key = reqKey /\ store[key] = value
               \/ op = "delete" /\ key = reqKey /\ store[key] = Sentinel

ReturnValueCorrectness ==
    \A request \in DOMAIN requests :
        LET response == ProcessRequest(request)
            op == request[1]
            key == request[2]
            value == IF op \in {"insert", "update"} THEN request[3] ELSE Sentinel
        IN
           \/ op = "get" /\ (store[key] = Sentinel <=> response[2] = Sentinel) 
           \/ op = "insert" /\ (store[key] = Sentinel => response[2] = "ok")
           \/ op = "update" /\ (store[key] \= Sentinel => response[2] = "ok")
           \/ op = "delete" /\ response[2] = "ok"

\* Temporal properties
Progress ==
    WF_<<requests>>_Next

EventualService ==
    SF_<<responses>>_Next

END ALGORITHM *)

=============================================================================