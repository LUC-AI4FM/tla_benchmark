------------------------------ MODULE KeyValueStore ------------------------------
(***************************************************************************)
(* Abstract model of a single-node key-value store with four operations:   *)
(* get, insert, update and delete. Each operation has a request transition *)
(* and a matching response transition. Each client has at most one         *)
(* outstanding request, so every response is paired with the most recent  *)
(* request of that client that has not yet completed.                      *)
(* A ghost history (log) of completed operations supports checking state   *)
(* consistency and return-value correctness.                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Keys,       \* finite universe of keys
    Vals,       \* finite universe of values
    Clients,    \* finite set of clients issuing requests
    Missing,    \* sentinel value for "key absent" / nil
    Ok,         \* sentinel result "ok"
    Err,        \* sentinel result "error"
    MaxOps      \* bound on history length, used only by the state constraint

ASSUME KeysNonEmpty   == Keys # {}
ASSUME ClientsNonEmpty == Clients # {}
ASSUME SentinelsDistinct ==
    /\ Missing \notin Vals
    /\ Ok \notin Vals
    /\ Err \notin Vals
    /\ Missing # Ok /\ Missing # Err /\ Ok # Err
ASSUME MaxOpsNat == MaxOps \in Nat

VARIABLES
    store,  \* abstract mapping: Keys -> Vals \cup {Missing}
    req,    \* req[c]: outstanding request of client c, or NoReq
    resp,   \* resp[c]: last response delivered to client c, or NoResp(c)
    log     \* ghost: sequence of completed operations

vars == <<store, req, resp, log>>

-----------------------------------------------------------------------------
Ops      == {"get", "insert", "update", "delete"}
StoreVal == Vals \cup {Missing}
Results  == Vals \cup {Missing, Ok, Err}
Mappings == [Keys -> StoreVal]

InitStore == [k \in Keys |-> Missing]

AnyKey == CHOOSE k \in Keys : TRUE

Requests ==
         [op : {"get", "delete"}, key : Keys, val : {Missing}]
    \cup [op : {"insert", "update"}, key : Keys, val : Vals]

NoReq == [op |-> "none", key |-> AnyKey, val |-> Missing]

Entries ==
    [client : Clients, op : Ops, key : Keys, val : StoreVal,
     pre : Mappings, post : Mappings, result : Results]

NoResp(c) ==
    [client |-> c, op |-> "none", key |-> AnyKey, val |-> Missing,
     pre |-> InitStore, post |-> InitStore, result |-> Missing]

-----------------------------------------------------------------------------
(* Specified semantics of each operation, as functions of the pre-state.  *)

ResultOf(m, op, k, v) ==
    CASE op = "get"    -> m[k]
      [] op = "insert" -> IF m[k] = Missing THEN Ok ELSE Err
      [] op = "update" -> IF m[k] # Missing THEN Ok ELSE Err
      [] op = "delete" -> Ok

ApplyOp(m, op, k, v) ==
    CASE op = "get"    -> m
      [] op = "insert" -> IF m[k] = Missing THEN [m EXCEPT ![k] = v] ELSE m
      [] op = "update" -> IF m[k] # Missing THEN [m EXCEPT ![k] = v] ELSE m
      [] op = "delete" -> [m EXCEPT ![k] = Missing]

RECURSIVE Replay(_, _)
Replay(m, s) ==
    IF s = << >> THEN m
    ELSE Replay(ApplyOp(m, Head(s).op, Head(s).key, Head(s).val), Tail(s))

-----------------------------------------------------------------------------
Init ==
    /\ store = InitStore
    /\ req   = [c \in Clients |-> NoReq]
    /\ resp  = [c \in Clients |-> NoResp(c)]
    /\ log   = << >>

(* A client with no outstanding request issues a new one. *)
Request(c) ==
    /\ req[c] = NoReq
    /\ \E r \in Requests : req' = [req EXCEPT ![c] = r]
    /\ UNCHANGED <<store, resp, log>>

(* The store atomically executes the outstanding request of client c and  *)
(* delivers the matching response.                                         *)
Respond(c) ==
    /\ req[c] # NoReq
    /\ LET r     == req[c]
           res   == ResultOf(store, r.op, r.key, r.val)
           post  == ApplyOp(store, r.op, r.key, r.val)
           entry == [client |-> c, op |-> r.op, key |-> r.key, val |-> r.val,
                     pre |-> store, post |-> post, result |-> res]
       IN  /\ store' = post
           /\ resp'  = [resp EXCEPT ![c] = entry]
           /\ log'   = Append(log, entry)
           /\ req'   = [req EXCEPT ![c] = NoReq]

Next == \E c \in Clients : Request(c) \/ Respond(c)

Fairness == \A c \in Clients : WF_vars(Respond(c))

Spec == Init /\ [][Next]_vars /\ Fairness

(* State constraint for bounded model checking of the ghost history. *)
StateConstraint == Len(log) <= MaxOps

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ store \in Mappings
    /\ req   \in [Clients -> Requests \cup {NoReq}]
    /\ \A c \in Clients : resp[c] \in Entries \cup {NoResp(c)}
    /\ log   \in Seq(Entries)

(* State consistency: the store reflects exactly the effects of all       *)
(* completed operations, in completion order.                              *)
StateConsistency == store = Replay(InitStore, log)

(* The pre/post states recorded in the history chain correctly. *)
HistoryChained ==
    /\ Len(log) > 0 => log[1].pre = InitStore
    /\ \A i \in 1..(Len(log) - 1) : log[i + 1].pre = log[i].post
    /\ Len(log) > 0 => log[Len(log)].post = store

(* Return-value correctness: each response is correct w.r.t. the pre-state *)
(* at the time it was generated, and the mapping was updated accordingly.  *)
EntryCorrect(e) ==
    /\ e.result = ResultOf(e.pre, e.op, e.key, e.val)
    /\ e.post   = ApplyOp(e.pre, e.op, e.key, e.val)
    /\ e.op = "get"    => e.result = e.pre[e.key]
    /\ e.op = "insert" => /\ (e.result = Ok <=> e.pre[e.key] = Missing)
                          /\ e.result = Ok  => e.post[e.key] = e.val
                          /\ e.result = Err => e.post = e.pre
    /\ e.op = "update" => /\ (e.result = Ok <=> e.pre[e.key] # Missing)
                          /\ e.result = Ok  => e.post[e.key] = e.val
                          /\ e.result = Err => e.post = e.pre
    /\ e.op = "delete" => /\ e.result = Ok
                          /\ e.post[e.key] = Missing

ReturnValueCorrectness == \A i \in 1..Len(log) : EntryCorrect(log[i])

(* Request/response pairing: a client's last response is its most recent  *)
(* completed operation in the history.                                     *)
ResponsePairing ==
    \A c \in Clients :
        resp[c] # NoResp(c) =>
            \E i \in 1..Len(log) :
                /\ log[i] = resp[c]
                /\ \A j \in (i + 1)..Len(log) : log[j].client # c

Safety ==
    /\ TypeOK
    /\ StateConsistency
    /\ HistoryChained
    /\ ReturnValueCorrectness
    /\ ResponsePairing

(* Action property: every response answers exactly the outstanding request *)
(* of that client, and only clients with an outstanding request respond.   *)
ResponseMatchesRequest ==
    [][\A c \in Clients :
         resp'[c] # resp[c] =>
            /\ req[c] # NoReq
            /\ req'[c] = NoReq
            /\ resp'[c].op  = req[c].op
            /\ resp'[c].key = req[c].key
            /\ resp'[c].val = req[c].val]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Progress: every issued request eventually receives its response. *)
Progress ==
    \A c \in Clients : (req[c] # NoReq) ~> (req[c] = NoReq)

(* Eventual service: if requests keep being issued, responses keep being   *)
(* produced; the system never stalls permanently.                          *)
EventualService ==
    []<>(\E c \in Clients : req[c] # NoReq)
        => []<><<\E c \in Clients : Respond(c)>>_vars

(* No permanent stall with an outstanding request. *)
NoPermanentStall ==
    \A c \in Clients : ~<>[](req[c] # NoReq)

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => ResponseMatchesRequest
THEOREM Spec => Progress /\ EventualService /\ NoPermanentStall
=============================================================================