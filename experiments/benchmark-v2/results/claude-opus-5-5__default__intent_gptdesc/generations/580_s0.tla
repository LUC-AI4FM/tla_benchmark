------------------------------- MODULE BoundedTxnNode -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Keys,          \* the set of keys stored by the node
    Values,        \* the set of values a key may hold
    NoVal,         \* placeholder value, not a member of Values
    MaxHistory     \* bound on the number of history entries

ASSUME ConstantsOK ==
    /\ Keys # {}
    /\ Values # {}
    /\ NoVal \notin Values
    /\ MaxHistory \in Nat
    /\ MaxHistory >= 1

(*************************************************************************)
(* Every request uses one history slot, so MaxHistory bounds request ids. *)
(*************************************************************************)
ReqIds == 1..MaxHistory

AnyKey == CHOOSE k \in Keys : TRUE

VARIABLES
    store,      \* the node's current key/value state
    history,    \* bounded log of requests, responses and read-write ops
    pending,    \* ids of read-only requests accepted but not yet answered
    responded,  \* ids of read-only requests that have been answered
    nextId,     \* next fresh request id
    reqKey,     \* key read by each read-only request
    window      \* values the key held between the request's accept and its response

vars == <<store, history, pending, responded, nextId, reqKey, window>>

Entry == [type : {"ro_req", "ro_resp", "rw"},
          id   : ReqIds \cup {0},
          key  : Keys,
          val  : Values \cup {NoVal}]

(*************************************************************************)
(* Space reservation.  Every pending request keeps one history slot free *)
(* for its response, so admitted requests can always be answered.        *)
(*************************************************************************)
Used == Len(history) + Cardinality(pending)

TypeOK ==
    /\ store \in [Keys -> Values]
    /\ history \in Seq(Entry)
    /\ pending \subseteq ReqIds
    /\ responded \subseteq ReqIds
    /\ nextId \in 1..(MaxHistory + 1)
    /\ reqKey \in [ReqIds -> Keys]
    /\ window \in [ReqIds -> SUBSET Values]

-----------------------------------------------------------------------------
Init ==
    /\ store \in [Keys -> Values]
    /\ history = << >>
    /\ pending = {}
    /\ responded = {}
    /\ nextId = 1
    /\ reqKey = [i \in ReqIds |-> AnyKey]
    /\ window = [i \in ReqIds |-> {}]

(*************************************************************************)
(* Accept a read-only transaction request for key k.  The request is      *)
(* admitted only if it leaves room for its own request entry and for the *)
(* responses of every pending request.                                    *)
(*************************************************************************)
AcceptRO(k) ==
    /\ nextId \in ReqIds
    /\ Used + 2 <= MaxHistory
    /\ history' = Append(history,
                    [type |-> "ro_req", id |-> nextId, key |-> k, val |-> NoVal])
    /\ pending' = pending \cup {nextId}
    /\ reqKey' = [reqKey EXCEPT ![nextId] = k]
    /\ window' = [window EXCEPT ![nextId] = {store[k]}]
    /\ nextId' = nextId + 1
    /\ UNCHANGED <<store, responded>>

(*************************************************************************)
(* Produce the response to a pending read-only transaction.  The value    *)
(* returned is the current state of the key, and that moment is the      *)
(* linearization point.                                                  *)
(*************************************************************************)
RespondRO(id) ==
    /\ id \in pending
    /\ Len(history) < MaxHistory
    /\ history' = Append(history,
                    [type |-> "ro_resp", id |-> id, key |-> reqKey[id],
                     val |-> store[reqKey[id]]])
    /\ pending' = pending \ {id}
    /\ responded' = responded \cup {id}
    /\ UNCHANGED <<store, nextId, reqKey, window>>

(*************************************************************************)
(* Ordinary node action: internal processing of a read-write operation   *)
(* that updates key k to value v.  The write must not consume the slots  *)
(* reserved for pending responses.  Each pending read of k records v as  *)
(* a possible linearization value.                                        *)
(*************************************************************************)
NodeAction(k, v) ==
    /\ Used + 1 <= MaxHistory
    /\ store' = [store EXCEPT ![k] = v]
    /\ history' = Append(history,
                    [type |-> "rw", id |-> 0, key |-> k, val |-> v])
    /\ window' = [i \in ReqIds |->
                    IF i \in pending /\ reqKey[i] = k
                    THEN window[i] \cup {v}
                    ELSE window[i]]
    /\ UNCHANGED <<pending, responded, nextId, reqKey>>

(*************************************************************************)
(* System step when no request, response or node action occurs.          *)
(*************************************************************************)
Advance ==
    /\ UNCHANGED vars

Next ==
    \/ \E k \in Keys : AcceptRO(k)
    \/ \E id \in ReqIds : RespondRO(id)
    \/ \E k \in Keys, v \in Values : NodeAction(k, v)
    \/ Advance

(*************************************************************************)
(* Fairness: every admitted read-only request is eventually answered.    *)
(*************************************************************************)
Fairness == \A id \in ReqIds : WF_vars(RespondRO(id))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety properties *****************************)

\* The history never exceeds the configured cap.
HistoryBounded == Len(history) <= MaxHistory

\* Pending responses always have reserved space.
ReservationInv == Used <= MaxHistory

\* Every response corresponds to an earlier accepted request for the same
\* key, and no request is answered more than once.
ResponsesMatchRequests ==
    \A i \in 1..Len(history) :
        history[i].type = "ro_resp" =>
            /\ \E j \in 1..(i - 1) :
                  /\ history[j].type = "ro_req"
                  /\ history[j].id = history[i].id
                  /\ history[j].key = history[i].key
            /\ \A j \in 1..Len(history) :
                  (j # i /\ history[j].type = "ro_resp")
                      => history[j].id # history[i].id

\* Read-only responses return a value that the key held at some point
\* between the request's acceptance and its response.
ROLinearizable ==
    \A i \in 1..Len(history) :
        history[i].type = "ro_resp" =>
            history[i].val \in window[history[i].id]

\* Pending and responded requests are disjoint and were really issued.
RequestBookkeeping ==
    /\ pending \cap responded = {}
    /\ \A id \in pending \cup responded : id < nextId

Safety ==
    /\ TypeOK
    /\ HistoryBounded
    /\ ReservationInv
    /\ ResponsesMatchRequests
    /\ ROLinearizable
    /\ RequestBookkeeping

(*************************** Liveness properties ***************************)

\* Every admitted read-only request eventually gets a response.
EventualResponse ==
    \A id \in ReqIds : (id \in pending) ~> (id \in responded)

\* No request remains pending forever.
NoStarvation ==
    \A id \in ReqIds : []<>(id \notin pending)

THEOREM Spec => []Safety
THEOREM Spec => EventualResponse
=============================================================================