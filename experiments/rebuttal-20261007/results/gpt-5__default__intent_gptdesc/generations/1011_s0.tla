--------------------------- MODULE KVStore ---------------------------
EXTENDS Naturals, FiniteSets

(*
  Single-node key-value store with atomic request/response API for:
  get, insert, update, delete.
*)

CONSTANTS
  CLIENT,    \* finite set of clients
  KEYS,      \* finite set of keys
  VALUES,    \* finite set of values
  NIL,       \* distinguished sentinel for "missing" (not in VALUES)
  OK, ERR    \* result atoms for success/error (distinct from NIL and from each other)

ASSUME
  /\ IsFiniteSet(CLIENT)
  /\ IsFiniteSet(KEYS)
  /\ IsFiniteSet(VALUES)
  /\ NIL \notin VALUES
  /\ OK # ERR
  /\ OK # NIL
  /\ ERR # NIL
  /\ OK \notin VALUES
  /\ ERR \notin VALUES

(**********************************************************************
  State
**********************************************************************)

OpType == {"Get", "Insert", "Update", "Delete"}
VNil   == VALUES \cup {NIL}

RequestSet ==
  [ op: OpType, key: KEYS, val: VNil ]

NoReq  == "NoReq"
NoResp == "NoResp"

ResponseType ==
  [ client: CLIENT,
    op: OpType,
    key: KEYS,
    argVal: VNil,
    pre: [KEYS -> VNil],
    post: [KEYS -> VNil],
    status: {OK, ERR, NIL},
    retVal: VNil,
    prevReq: RequestSet
  ]

VARIABLES
  kv,        \* abstract store: total map KEYS -> VALUES \cup {NIL}
  pending,   \* per-client outstanding request or NoReq
  lastResp   \* info about the most recent completed response, or NoResp

Vars == << kv, pending, lastResp >>

(**********************************************************************
  Initialization
**********************************************************************)

Init ==
  /\ kv \in [KEYS -> VNil]
  /\ pending = [c \in CLIENT |-> NoReq]
  /\ lastResp = NoResp

(**********************************************************************
  Helpers
**********************************************************************)

ReqWF(r) ==
  /\ r \in RequestSet
  /\ IF r.op \in {"Insert","Update"} THEN r.val \in VALUES ELSE r.val = NIL

(**********************************************************************
  Actions
**********************************************************************)

Request(c, op, k, v) ==
  /\ c \in CLIENT /\ op \in OpType /\ k \in KEYS /\ v \in VNil
  /\ pending[c] = NoReq
  /\ IF op \in {"Insert","Update"} THEN v \in VALUES ELSE v = NIL
  /\ pending' = [pending EXCEPT ![c] = [op |-> op, key |-> k, val |-> v]]
  /\ kv' = kv
  /\ lastResp' = lastResp

Respond(c) ==
  /\ c \in CLIENT
  /\ pending[c] # NoReq
  /\ LET r == pending[c] IN
     LET k == r.key IN
     LET newKv ==
           CASE r.op = "Get"    -> kv
              [] r.op = "Insert" ->
                    IF kv[k] = NIL
                       THEN [kv EXCEPT ![k] = r.val]
                       ELSE kv
              [] r.op = "Update" ->
                    IF kv[k] # NIL
                       THEN [kv EXCEPT ![k] = r.val]
                       ELSE kv
              [] r.op = "Delete" -> [kv EXCEPT ![k] = NIL]
         status ==
           CASE r.op = "Get"    -> NIL
              [] r.op = "Insert" -> IF kv[k] = NIL THEN OK ELSE ERR
              [] r.op = "Update" -> IF kv[k] # NIL THEN OK ELSE ERR
              [] r.op = "Delete" -> OK
         ret ==
           CASE r.op = "Get"    -> kv[k]
              [] OTHER          -> status
     IN
     /\ kv' = newKv
     /\ pending' = [pending EXCEPT ![c] = NoReq]
     /\ lastResp' =
           [ client |-> c,
             op     |-> r.op,
             key    |-> r.key,
             argVal |-> r.val,
             pre    |-> kv,
             post   |-> newKv,
             status |-> status,
             retVal |-> ret,
             prevReq|-> r
           ]

Next ==
  \/ \E c \in CLIENT, op \in OpType, k \in KEYS, v \in VNil : Request(c, op, k, v)
  \/ \E c \in CLIENT : Respond(c)

(**********************************************************************
  Safety Invariants
**********************************************************************)

TypeOK ==
  /\ kv \in [KEYS -> VNil]
  /\ pending \in [CLIENT -> ({NoReq} \cup RequestSet)]
  /\ \A c \in CLIENT : pending[c] = NoReq \/ ReqWF(pending[c])
  /\ lastResp = NoResp \/ lastResp \in ResponseType

ReturnValueAndStateCorrect ==
  /\ lastResp = NoResp
  \/ LET r == lastResp IN
     /\ r.post = kv
     /\ r.prevReq = [op |-> r.op, key |-> r.key, val |-> r.argVal]
     /\ CASE r.op = "Get" ->
            /\ r.status = NIL
            /\ r.retVal = r.pre[r.key]
            /\ r.post = r.pre
        [] r.op = "Insert" ->
            IF r.pre[r.key] = NIL
              THEN /\ r.status = OK
                   /\ r.retVal = OK
                   /\ r.post = [r.pre EXCEPT ![r.key] = r.argVal]
              ELSE /\ r.status = ERR
                   /\ r.retVal = ERR
                   /\ r.post = r.pre
        [] r.op = "Update" ->
            IF r.pre[r.key] # NIL
              THEN /\ r.status = OK
                   /\ r.retVal = OK
                   /\ r.post = [r.pre EXCEPT ![r.key] = r.argVal]
              ELSE /\ r.status = ERR
                   /\ r.retVal = ERR
                   /\ r.post = r.pre
        [] r.op = "Delete" ->
            /\ r.status = OK
            /\ r.retVal = OK
            /\ r.post = [r.pre EXCEPT ![r.key] = NIL]

(*
  Each response corresponds to the client's most recent outstanding request,
  captured in lastResp.prevReq, and is computed from lastResp.pre.
*)
PairingOK ==
  /\ lastResp = NoResp
  \/ LET r == lastResp IN
     /\ r.prevReq \in RequestSet
     /\ r.prevReq.op = r.op
     /\ r.prevReq.key = r.key
     /\ r.prevReq.val = r.argVal

Safety ==
  TypeOK /\ ReturnValueAndStateCorrect /\ PairingOK

(**********************************************************************
  Liveness
**********************************************************************)

(*
  Any pending request is always immediately respondable.
*)
AlwaysEnabledRespond ==
  \A c \in CLIENT : [](pending[c] # NoReq => ENABLED Respond(c))

(*
  Progress: any issued request is eventually completed.
*)
OpProgress ==
  \A c \in CLIENT : [] (pending[c] # NoReq => <> pending[c] = NoReq)

(*
  Optional eventual service: if requests keep appearing infinitely often,
  responses also occur infinitely often (captured by lastResp changing from NoResp
  at least once and remaining as the latest response).
*)
EventualService ==
  [](<>(\E c \in CLIENT : pending[c] # NoReq) => <>(lastResp # NoResp))

(**********************************************************************
  Full Specification
**********************************************************************)

Spec ==
  Init
  /\ [][Next]_Vars
  /\ \A c \in CLIENT : WF_Vars(Respond(c))

======================================================================