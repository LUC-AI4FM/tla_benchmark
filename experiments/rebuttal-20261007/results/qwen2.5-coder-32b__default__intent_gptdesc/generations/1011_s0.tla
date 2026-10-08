------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys, Values, Sentinel

VARIABLES store, requests, responses

Init == /\ store \in [Keys -> {Sentinel} \cup Values]
        /\ requests = << >>
        /\ responses = << >>

GetOp(key) == \/ key \notin DOMAIN store
                \/ key \in DOMAIN store /\ store[key] = Sentinel

InsertOp(key, value) == key \notin DOMAIN store

UpdateOp(key, value) == key \in DOMAIN store /\ store[key] /= Sentinel

DeleteOp(key) == TRUE

RequestType == {"get", "insert", "update", "delete"}

Next ==
    \/ /\ requests = << >>
       /\ \E op \in RequestType, key \in Keys, value \in Values :
            \/ (op = "get" /\ GetOp(key))
            \/ (op = "insert" /\ InsertOp(key, value))
            \/ (op = "update" /\ UpdateOp(key, value))
            \/ (op = "delete" /\ DeleteOp(key))
          /\ requests' = Append(requests, <<op, key, value>>)
          /\ UNCHANGED <<store, responses>>
    \/ /\ requests /= << >>
       /\ LET req == Head(requests) IN
          CASE Fst(req) = "get" ->
               /\ GetOp(Snd(req))
               /\ store' = [store EXCEPT ![Snd(req)] = Sentinel]
               /\ responses' = Append(responses, IF Snd(req) \in DOMAIN store THEN <<Fst(req), Snd(req), store[Snd(req)]] ELSE <<Fst(req), Snd(req), Sentinel>>)
               /\ requests' = Tail(requests)
          [] Fst(req) = "insert" ->
               /\ InsertOp(Snd(req), Thrd(req))
               /\ store' = [store EXCEPT ![Snd(req)] = Thrd(req)]
               /\ responses' = Append(responses, <<Fst(req), Snd(req), "ok">>)
               /\ requests' = Tail(requests)
          [] Fst(req) = "update" ->
               /\ UpdateOp(Snd(req), Thrd(req))
               /\ store' = [store EXCEPT ![Snd(req)] = Thrd(req)]
               /\ responses' = Append(responses, <<Fst(req), Snd(req), "ok">>)
               /\ requests' = Tail(requests)
          [] Fst(req) = "delete" ->
               /\ DeleteOp(Snd(req))
               /\ store' = [store EXCEPT ![Snd(req)] = Sentinel]
               /\ responses' = Append(responses, <<Fst(req), Snd(req), "ok">>)
               /\ requests' = Tail(requests)

Spec == Init /\ [][Next]_<<store, requests, responses>>

StateConsistency ==
    \A key \in Keys :
        \/ store[key] = Sentinel
        \/ (\E op \in RequestType, value \in Values, req \in Seq(RequestType) :
            /\ <<op, key, value>> \in req
            /\ (op = "insert" \/ op = "update")
            /\ (\A prevOp \in req \cap {r \in Seq(RequestType) : r < <<op, key, value>>>} :
                (Fst(prevOp) # "delete" \/ Thrd(prevOp) /= store[key]))
            /\ (\E resp \in Seq(responses) :
                Fst(resp) = op /\ Snd(resp) = key))

ReturnValueCorrectness ==
    \A req \in Seq(requests), resp \in Seq(responses) :
        /\ Fst(req) = "get" ->
           (Snd(req) \notin DOMAIN store \/ store[Snd(req)] = Sentinel)
           /\ (Fst(resp) = "get" /\ Snd(resp) = Snd(req))
           /\ (Thrd(resp) = Sentinel \/ Thrd(resp) = store[Snd(req)])
        /\ Fst(req) = "insert" ->
           (Snd(req) \notin DOMAIN store)
           /\ (Fst(resp) = "insert" /\ Snd(resp) = Snd(req))
           /\ (Thrd(resp) = "ok" \/ Thrd(resp) = "error")
        /\ Fst(req) = "update" ->
           (Snd(req) \in DOMAIN store /\ store[Snd(req)] /= Sentinel)
           /\ (Fst(resp) = "update" /\ Snd(resp) = Snd(req))
           /\ (Thrd(resp) = "ok" \/ Thrd(resp) = "error")
        /\ Fst(req) = "delete" ->
           TRUE
           /\ (Fst(resp) = "delete" /\ Snd(resp) = Snd(req))
           /\ (Thrd(resp) = "ok")

Progress ==
    \A req \in Seq(requests) :
        \E resp \in Seq(responses) : Fst(req) = Fst(resp) /\ Snd(req) = Snd(resp)

EventuallyService ==
    \A req \in Seq(requests) :
        WF_seq_(<<requests, responses>>, _ >>_req)

=============================================================================