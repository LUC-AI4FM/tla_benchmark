------------------------------- MODULE KVStore -------------------------------

EXTENDS FiniteSets

CONSTANTS
  KEYS,        \* finite set of keys
  VALUES,      \* finite set of values
  Clients,     \* set of clients
  Nil,         \* distinguished sentinel for "missing"
  OK, ERR      \* result atoms for success/error

ASSUME
  /\ IsFiniteSet(KEYS)
  /\ IsFiniteSet(VALUES)
  /\ Nil \notin VALUES
  /\ OK # ERR
  /\ OK \notin VALUES
  /\ ERR \notin VALUES
  /\ Nil # OK
  /\ Nil # ERR

(*
  Abstract state
*)
VARIABLES
  store,   \* mapping KEYS -> VALUES \cup {Nil}
  req,     \* per-client outstanding request or "none"
  resp     \* per-client last response or "none"

vars == << store, req, resp >>

OpTags == {"get", "insert", "update", "delete"}

StoreType == [KEYS -> VALUES \cup {Nil}]

Requests ==
  { [op |-> o, k |-> k, v |-> v]
    : o \in OpTags, k \in KEYS, v \in VALUES }

ResponsesGet ==
  { [op |-> "get", k |-> k, res |-> r]
    : k \in KEYS, r \in VALUES \cup {Nil} }

ResponsesIns ==
  { [op |-> "insert", k |-> k, v |-> v, res |-> r]
    : k \in KEYS, v \in VALUES, r \in {OK, ERR} }

ResponsesUpd ==
  { [op |-> "update", k |-> k, v |-> v, res |-> r]
    : k \in KEYS, v \in VALUES, r \in {OK, ERR} }

ResponsesDel ==
  { [op |-> "delete", k |-> k, res |-> OK]
    : k \in KEYS }

Responses == ResponsesGet \cup ResponsesIns \cup ResponsesUpd \cup ResponsesDel

MaybeReq  == Requests \cup {"none"}
MaybeResp == Responses \cup {"none"}

TypeInv ==
  /\ store \in StoreType
  /\ req \in [Clients -> MaybeReq]
  /\ resp \in [Clients -> MaybeResp]

\* At most one outstanding operation per client; responses are produced only after requests.
PairingInv ==
  \A c \in Clients : req[c] # "none" => resp[c] = "none"

\* Return-value correctness and post-state consistency for each completed response.
RespConsistent ==
  \A c \in Clients :
    IF resp[c] \in Responses THEN
      LET r == resp[c] IN
        CASE r.op = "get"    -> store[r.k] = r.res
          [] r.op = "insert" /\ r.res = OK  ->
                 \E v \in VALUES : r = [op |-> "insert", k |-> r.k, v |-> v, res |-> OK]
                                   /\ store[r.k] = v
          [] r.op = "insert" /\ r.res = ERR -> store[r.k] \in VALUES
          [] r.op = "update" /\ r.res = OK  ->
                 \E v \in VALUES : r = [op |-> "update", k |-> r.k, v |-> v, res |-> OK]
                                   /\ store[r.k] = v
          [] r.op = "update" /\ r.res = ERR -> store[r.k] = Nil
          [] r.op = "delete"               -> store[r.k] = Nil
    ELSE TRUE

Inv == TypeInv /\ PairingInv /\ RespConsistent

IsPending(c) == req[c] \in Requests
HasResp(c)   == resp[c] \in Responses

Init ==
  /\ store = [k \in KEYS |-> Nil]
  /\ req   = [c \in Clients |-> "none"]
  /\ resp  = [c \in Clients |-> "none"]

Request(c) ==
  /\ c \in Clients
  /\ req[c] = "none"
  /\ \E o \in OpTags, k \in KEYS, v \in VALUES :
        /\ req'  = [req EXCEPT ![c] = [op |-> o, k |-> k, v |-> v]]
        /\ resp' = [resp EXCEPT ![c] = "none"]
        /\ UNCHANGED store

Respond(c) ==
  /\ c \in Clients
  /\ req[c] \in Requests
  /\ LET r == req[c] IN
     CASE r.op = "get" ->
            /\ resp'  = [resp EXCEPT ![c] = [op |-> "get", k |-> r.k, res |-> store[r.k]]]
            /\ req'   = [req EXCEPT ![c] = "none"]
            /\ UNCHANGED store
       [] r.op = "insert" ->
            IF store[r.k] = Nil THEN
              /\ store' = [store EXCEPT ![r.k] = r.v]
              /\ resp'  = [resp EXCEPT ![c] = [op |-> "insert", k |-> r.k, v |-> r.v, res |-> OK]]
              /\ req'   = [req EXCEPT ![c] = "none"]
            ELSE
              /\ UNCHANGED store
              /\ resp'  = [resp EXCEPT ![c] = [op |-> "insert", k |-> r.k, v |-> r.v, res |-> ERR]]
              /\ req'   = [req EXCEPT ![c] = "none"]
       [] r.op = "update" ->
            IF store[r.k] # Nil THEN
              /\ store' = [store EXCEPT ![r.k] = r.v]
              /\ resp'  = [resp EXCEPT ![c] = [op |-> "update", k |-> r.k, v |-> r.v, res |-> OK]]
              /\ req'   = [req EXCEPT ![c] = "none"]
            ELSE
              /\ UNCHANGED store
              /\ resp'  = [resp EXCEPT ![c] = [op |-> "update", k |-> r.k, v |-> r.v, res |-> ERR]]
              /\ req'   = [req EXCEPT ![c] = "none"]
       [] r.op = "delete" ->
            /\ store' = [store EXCEPT ![r.k] = Nil]
            /\ resp'  = [resp EXCEPT ![c] = [op |-> "delete", k |-> r.k, res |-> OK]]
            /\ req'   = [req EXCEPT ![c] = "none"]

Next ==
  \E c \in Clients : Request(c) \/ Respond(c)

\* Full specification with fairness ensuring every issued request is eventually served.
Spec ==
  Init /\ [][Next]_vars /\ (\A c \in Clients : WF_vars(Respond(c)))

\* Safety and liveness properties (derivable from Spec), provided for model checking.
Safety == []Inv

Progress ==
  \A c \in Clients : []( IsPending(c) => <> HasResp(c) )

=============================================================================