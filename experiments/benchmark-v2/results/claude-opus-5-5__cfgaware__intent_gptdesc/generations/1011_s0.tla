------------------------------- MODULE KVStore -------------------------------
(***************************************************************************)
(* An abstract model of a single-node key-value store with four            *)
(* client-visible operations: get, insert, update, and delete.             *)
(*                                                                         *)
(* Each operation has two parts: a request transition that issues it and   *)
(* a response transition that completes it atomically and returns a       *)
(* result. At most one request is outstanding at a time, so every          *)
(* response pairs with the most recently issued, not-yet-completed         *)
(* request.                                                                *)
(*                                                                         *)
(*   MISSING : the store marker for an absent key                          *)
(*   NIL     : the result of get on an absent key, and the filler for      *)
(*             unused fields                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Keys,     \* finite universe of keys
          Vals,     \* finite universe of values
          NIL,      \* "nil" sentinel (get on absent key / empty fields)
          MISSING   \* "missing" sentinel stored for absent keys

ASSUME /\ IsFiniteSet(Keys)
       /\ IsFiniteSet(Vals)
       /\ NIL \notin Vals
       /\ MISSING \notin Vals
       /\ NIL # MISSING

VARIABLES store,      \* abstract mapping: Keys -> Vals \cup {MISSING}
          busy,       \* TRUE iff a request is outstanding
          req,        \* the outstanding request (or NoReq)
          last,       \* ghost: record of the most recently completed operation
          prevStore   \* ghost: store just before the most recent response

vars == <<store, busy, req, last, prevStore>>

-----------------------------------------------------------------------------
Ops      == {"get", "insert", "update", "delete"}
Results  == Vals \cup {NIL, "ok", "error"}
StoreVal == Vals \cup {MISSING}

NoReq  == [op |-> "none", key |-> NIL, val |-> NIL]
NoLast == [op |-> "none", key |-> NIL, val |-> NIL,
           pre |-> NIL, post |-> NIL, result |-> NIL]

ReqType == [op : {"get", "delete"}, key : Keys, val : {NIL}]
             \cup [op : {"insert", "update"}, key : Keys, val : Vals]

LastType == [op : {"get", "delete"}, key : Keys, val : {NIL},
             pre : StoreVal, post : StoreVal, result : Results]
              \cup
            [op : {"insert", "update"}, key : Keys, val : Vals,
             pre : StoreVal, post : StoreVal, result : Results]

TypeOK ==
  /\ store \in [Keys -> StoreVal]
  /\ prevStore \in [Keys -> StoreVal]
  /\ busy \in BOOLEAN
  /\ req \in ReqType \cup {NoReq}
  /\ last \in LastType \cup {NoLast}
  /\ (busy <=> req # NoReq)

-----------------------------------------------------------------------------
Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ prevStore = [k \in Keys |-> MISSING]
  /\ busy = FALSE
  /\ req = NoReq
  /\ last = NoLast

(* ---------------------------- Requests --------------------------------- *)
Issue(r) ==
  /\ ~busy
  /\ busy' = TRUE
  /\ req' = r
  /\ UNCHANGED <<store, last, prevStore>>

RequestGet(k)       == Issue([op |-> "get",    key |-> k, val |-> NIL])
RequestInsert(k, v) == Issue([op |-> "insert", key |-> k, val |-> v])
RequestUpdate(k, v) == Issue([op |-> "update", key |-> k, val |-> v])
RequestDelete(k)    == Issue([op |-> "delete", key |-> k, val |-> NIL])

Request ==
  \/ \E k \in Keys : RequestGet(k)
  \/ \E k \in Keys : RequestDelete(k)
  \/ \E k \in Keys, v \in Vals : RequestInsert(k, v)
  \/ \E k \in Keys, v \in Vals : RequestUpdate(k, v)

(* ---------------------------- Response --------------------------------- *)
ResultOf(op, pre) ==
  CASE op = "get"    -> IF pre # MISSING THEN pre ELSE NIL
    [] op = "insert" -> IF pre = MISSING THEN "ok" ELSE "error"
    [] op = "update" -> IF pre # MISSING THEN "ok" ELSE "error"
    [] op = "delete" -> "ok"

PostOf(op, pre, v) ==
  CASE op = "insert" /\ pre = MISSING -> v
    [] op = "update" /\ pre # MISSING -> v
    [] op = "delete"                  -> MISSING
    [] OTHER                          -> pre

Respond ==
  /\ busy
  /\ LET k   == req.key
         v   == req.val
         pre == store[k]
         new == PostOf(req.op, pre, v)
     IN /\ store' = [store EXCEPT ![k] = new]
        /\ prevStore' = store
        /\ last' = [op |-> req.op, key |-> k, val |-> v,
                    pre |-> pre, post |-> new,
                    result |-> ResultOf(req.op, pre)]
  /\ busy' = FALSE
  /\ req' = NoReq

Next == Request \/ Respond

Spec == Init /\ [][Next]_vars /\ WF_vars(Respond)

-----------------------------------------------------------------------------
(* ----------------------------- Safety ---------------------------------- *)

\* Return-value correctness against the pre-state at response time.
ReturnCorrect ==
  last # NoLast =>
    /\ last.pre = prevStore[last.key]
    /\ (last.op = "get" =>
          last.result = IF last.pre = MISSING THEN NIL ELSE last.pre)
    /\ (last.op = "insert" =>
          (last.result = "ok" <=> last.pre = MISSING))
    /\ (last.op = "update" =>
          (last.result = "ok" <=> last.pre # MISSING))
    /\ (last.op = "delete" => last.result = "ok")
    /\ last.result \in IF last.op \in {"insert", "update"}
                         THEN {"ok", "error"}
                         ELSE IF last.op = "delete" THEN {"ok"}
                              ELSE Vals \cup {NIL}

\* State consistency: the mapping reflects the effect of the last completed
\* operation applied to the state that held before it, with no other key changed.
StateConsistent ==
  last # NoLast =>
    /\ store[last.key] = last.post
    /\ \A k \in Keys \ {last.key} : store[k] = prevStore[k]
    /\ (last.op = "get"    => last.post = last.pre)
    /\ (last.op = "insert" =>
          last.post = IF last.pre = MISSING THEN last.val ELSE last.pre)
    /\ (last.op = "update" =>
          last.post = IF last.pre # MISSING THEN last.val ELSE MISSING)
    /\ (last.op = "delete" => last.post = MISSING)

\* Pending requests do not mutate the store.
NoEffectWhilePending ==
  [][~busy /\ busy' => store' = store]_vars

\* Only the requested key changes on a response.
FrameCondition ==
  [][Respond => \A k \in Keys \ {req.key} : store'[k] = store[k]]_vars

\* The response pairs with the outstanding request.
ResponseMatchesRequest ==
  [][Respond => /\ last'.op = req.op
                /\ last'.key = req.key
                /\ last'.val = req.val]_vars

Safety == TypeOK /\ ReturnCorrect /\ StateConsistent

(* ----------------------------- Liveness -------------------------------- *)

\* Every issued request eventually receives its response.
Progress == busy ~> ~busy

\* Each specific request is eventually answered.
RequestAnswered ==
  \A k \in Keys :
    \A o \in Ops :
      (busy /\ req.op = o /\ req.key = k) ~>
        (~busy /\ last.op = o /\ last.key = k)

\* The system never stalls permanently with a pending request.
EventualService == []<>(~busy)

=============================================================================