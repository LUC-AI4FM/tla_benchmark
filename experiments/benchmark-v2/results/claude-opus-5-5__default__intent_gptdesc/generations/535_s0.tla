---------------------------- MODULE ConcurrentRecordStore ----------------------------
(***************************************************************************)
(* A concurrent store of multi-field records.  Each record has an         *)
(* immutable key field and a set of mutable value fields.  Clients        *)
(* invoke read, update (one or more fields), insert, and delete           *)
(* operations by sending requests over an unordered, delaying network.    *)
(* The server applies each request in one atomic step, which is its       *)
(* linearization point, and replies over the network.  Clients may        *)
(* request writes of the sentinel minimum value.  The server must reject  *)
(* these writes so that no record ever holds an invalid value.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Clients,     \* client process identifiers
    Faulty,      \* clients that may crash (not "correct")
    Keys,        \* universe of possible keys
    Fields,      \* names of the mutable value fields
    Values,      \* agreed valid domain for field values
    Sentinel,    \* designated sentinel minimum value (invalid)
    Capacity,    \* maximum number of records in the store
    MaxOps       \* bound on operations per client (for model checking)

ASSUME Faulty \subseteq Clients
ASSUME Sentinel \notin Values
ASSUME Fields # {} /\ Values # {}
ASSUME Capacity \in Nat /\ MaxOps \in Nat

Ops         == {"read", "update", "insert", "delete"}
WriteOps    == {"update", "insert", "delete"}
Statuses    == {"none", "ok", "notfound", "exists", "full", "rejected"}
InputValues == Values \cup {Sentinel}

\* Partial assignments for multi-field updates (one or more fields)
PartialUpdates == UNION { [F -> InputValues] : F \in (SUBSET Fields) \ {{}} }

ValsFor(op) ==
    CASE op = "update" -> PartialUpdates
      [] op = "insert" -> [Fields -> InputValues]
      [] OTHER         -> { <<>> }

VARIABLES
    store,      \* set of records [key, val, ver]
    verCtr,     \* ghost: per-key version counter, incremented by every applied write
    written,    \* ghost: every record version ever installed in the store
    complVer,   \* ghost: per-key highest version of a write whose response was received
    reqNet,     \* in-flight requests (unordered; delivery delayed nondeterministically)
    respNet,    \* in-flight responses
    pc,         \* client control state: "idle" or "waiting"
    seq,        \* per-client request sequence number
    opsDone,    \* per-client count of completed operations
    crashed,    \* per-client crash flag (only Faulty clients can crash)
    lastResp    \* last response observed by each client

clientVars == <<pc, seq, opsDone, crashed, lastResp>>
vars == <<store, verCtr, written, complVer, reqNet, respNet,
          pc, seq, opsDone, crashed, lastResp>>

KeysIn(S)      == { r.key : r \in S }
Lookup(k)      == CHOOSE r \in store : r.key = k
ValidVals(f)   == \A x \in DOMAIN f : f[x] \in Values

NoResp(c) == [client |-> c, seq |-> 0, op |-> "read", key |-> CHOOSE k \in Keys : TRUE,
              status |-> "none", val |-> <<>>, ver |-> 0, minVer |-> 0]

Resp(m, st, v, ver) ==
    [client |-> m.client, seq |-> m.seq, op |-> m.op, key |-> m.key,
     status |-> st, val |-> v, ver |-> ver, minVer |-> complVer[m.key]]

-----------------------------------------------------------------------------
TypeOK ==
    /\ store \subseteq [key : Keys, val : [Fields -> InputValues], ver : Nat]
    /\ verCtr \in [Keys -> Nat]
    /\ complVer \in [Keys -> Nat]
    /\ written \subseteq [key : Keys, val : [Fields -> InputValues], ver : Nat]
    /\ \A m \in reqNet : m.client \in Clients /\ m.op \in Ops /\ m.key \in Keys
    /\ \A m \in respNet : m.client \in Clients /\ m.status \in Statuses
    /\ pc \in [Clients -> {"idle", "waiting"}]
    /\ seq \in [Clients -> Nat]
    /\ opsDone \in [Clients -> 0..MaxOps]
    /\ crashed \in [Clients -> BOOLEAN]

Init ==
    /\ store = {}
    /\ verCtr = [k \in Keys |-> 0]
    /\ written = {}
    /\ complVer = [k \in Keys |-> 0]
    /\ reqNet = {}
    /\ respNet = {}
    /\ pc = [c \in Clients |-> "idle"]
    /\ seq = [c \in Clients |-> 0]
    /\ opsDone = [c \in Clients |-> 0]
    /\ crashed = [c \in Clients |-> FALSE]
    /\ lastResp = [c \in Clients |-> NoResp(c)]

-----------------------------------------------------------------------------
(* Client invokes an arbitrary operation. *)
Invoke(c) ==
    /\ ~crashed[c]
    /\ pc[c] = "idle"
    /\ opsDone[c] < MaxOps
    /\ \E op \in Ops, k \in Keys :
         \E vals \in ValsFor(op) :
            reqNet' = reqNet \cup
                {[client |-> c, seq |-> seq[c] + 1, op |-> op, key |-> k, vals |-> vals]}
    /\ seq' = [seq EXCEPT ![c] = @ + 1]
    /\ pc' = [pc EXCEPT ![c] = "waiting"]
    /\ UNCHANGED <<store, verCtr, written, complVer, respNet, opsDone, crashed, lastResp>>

(* Server: atomic read (linearization point). *)
ServerRead(m) ==
    /\ m.op = "read"
    /\ reqNet' = reqNet \ {m}
    /\ IF m.key \in KeysIn(store)
         THEN respNet' = respNet \cup {Resp(m, "ok", Lookup(m.key).val, verCtr[m.key])}
         ELSE respNet' = respNet \cup {Resp(m, "notfound", <<>>, verCtr[m.key])}
    /\ UNCHANGED <<store, verCtr, written, complVer, clientVars>>

(* Server: atomic multi-field update. *)
ServerUpdate(m) ==
    /\ m.op = "update"
    /\ reqNet' = reqNet \ {m}
    /\ IF ~ValidVals(m.vals)
         THEN /\ respNet' = respNet \cup {Resp(m, "rejected", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr, written>>
       ELSE IF m.key \notin KeysIn(store)
         THEN /\ respNet' = respNet \cup {Resp(m, "notfound", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr, written>>
       ELSE LET old    == Lookup(m.key)
                nv     == verCtr[m.key] + 1
                newVal == [f \in Fields |->
                              IF f \in DOMAIN m.vals THEN m.vals[f] ELSE old.val[f]]
                newRec == [key |-> m.key, val |-> newVal, ver |-> nv]
            IN /\ store' = (store \ {old}) \cup {newRec}
               /\ verCtr' = [verCtr EXCEPT ![m.key] = nv]
               /\ written' = written \cup {newRec}
               /\ respNet' = respNet \cup {Resp(m, "ok", newVal, nv)}
    /\ UNCHANGED <<complVer, clientVars>>

(* Server: atomic insert within capacity. *)
ServerInsert(m) ==
    /\ m.op = "insert"
    /\ reqNet' = reqNet \ {m}
    /\ IF ~ValidVals(m.vals)
         THEN /\ respNet' = respNet \cup {Resp(m, "rejected", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr, written>>
       ELSE IF m.key \in KeysIn(store)
         THEN /\ respNet' = respNet \cup {Resp(m, "exists", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr, written>>
       ELSE IF Cardinality(store) >= Capacity
         THEN /\ respNet' = respNet \cup {Resp(m, "full", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr, written>>
       ELSE LET nv     == verCtr[m.key] + 1
                newRec == [key |-> m.key, val |-> m.vals, ver |-> nv]
            IN /\ store' = store \cup {newRec}
               /\ verCtr' = [verCtr EXCEPT ![m.key] = nv]
               /\ written' = written \cup {newRec}
               /\ respNet' = respNet \cup {Resp(m, "ok", m.vals, nv)}
    /\ UNCHANGED <<complVer, clientVars>>

(* Server: atomic delete. *)
ServerDelete(m) ==
    /\ m.op = "delete"
    /\ reqNet' = reqNet \ {m}
    /\ IF m.key \notin KeysIn(store)
         THEN /\ respNet' = respNet \cup {Resp(m, "notfound", <<>>, verCtr[m.key])}
              /\ UNCHANGED <<store, verCtr>>
         ELSE LET nv == verCtr[m.key] + 1
              IN /\ store' = store \ {Lookup(m.key)}
                 /\ verCtr' = [verCtr EXCEPT ![m.key] = nv]
                 /\ respNet' = respNet \cup {Resp(m, "ok", <<>>, nv)}
    /\ UNCHANGED <<written, complVer, clientVars>>

ServerApply(m) ==
    \/ ServerRead(m)
    \/ ServerUpdate(m)
    \/ ServerInsert(m)
    \/ ServerDelete(m)

(* The server serves the pending request of client c (any interleaving). *)
ServerStep(c) == \E m \in reqNet : m.client = c /\ ServerApply(m)

(* Client receives its response after an arbitrary delay. *)
Receive(c) ==
    /\ ~crashed[c]
    /\ pc[c] = "waiting"
    /\ \E m \in respNet :
         /\ m.client = c
         /\ m.seq = seq[c]
         /\ respNet' = respNet \ {m}
         /\ lastResp' = [lastResp EXCEPT ![c] = m]
         /\ complVer' = IF m.op \in WriteOps /\ m.status = "ok"
                          THEN [complVer EXCEPT ![m.key] =
                                   IF m.ver > @ THEN m.ver ELSE @]
                          ELSE complVer
    /\ pc' = [pc EXCEPT ![c] = "idle"]
    /\ opsDone' = [opsDone EXCEPT ![c] = @ + 1]
    /\ UNCHANGED <<store, verCtr, written, reqNet, seq, crashed>>

(* A faulty client may crash at any time. *)
Crash(c) ==
    /\ c \in Faulty
    /\ ~crashed[c]
    /\ crashed' = [crashed EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<store, verCtr, written, complVer, reqNet, respNet,
                   pc, seq, opsDone, lastResp>>

(* Stuttering once all work is finished, to avoid spurious deadlock. *)
Terminated ==
    /\ reqNet = {}
    /\ \A c \in Clients : crashed[c] \/ (pc[c] = "idle" /\ opsDone[c] = MaxOps)
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Clients : Invoke(c) \/ ServerStep(c) \/ Receive(c) \/ Crash(c)
    \/ Terminated

Fairness ==
    /\ \A c \in Clients : WF_vars(ServerStep(c))
    /\ \A c \in Clients \ Faulty : WF_vars(Receive(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** SAFETY INVARIANTS *****************************)

AllObserved == respNet \cup { lastResp[c] : c \in Clients }

\* Keys uniquely identify records
KeyUniqueness ==
    \A r1, r2 \in store : r1.key = r2.key => r1 = r2

\* Capacity is never exceeded
CapacityBound == Cardinality(store) <= Capacity

\* Every stored field value lies in the agreed domain
DomainConstraint ==
    \A r \in store : \A f \in Fields : r.val[f] \in Values

\* No record is ever created with the sentinel minimum value
NoSentinelCreated ==
    /\ \A r \in store : \A f \in Fields : r.val[f] # Sentinel
    /\ \A w \in written : \A f \in Fields : w.val[f] # Sentinel

\* No reader ever observes the sentinel value
NoSentinelObserved ==
    \A m \in AllObserved :
        (m.status = "ok") => \A f \in DOMAIN m.val : m.val[f] # Sentinel

\* Writes containing the sentinel are always rejected
SentinelWritesRejected ==
    \A m \in AllObserved :
        (m.op \in {"update", "insert"} /\ m.status = "ok") =>
            \A f \in DOMAIN m.val : m.val[f] \in Values

\* No torn or partial reads: every successful read returns a complete
\* record version that was atomically installed by a single write.
NoTornReads ==
    \A m \in AllObserved :
        (m.op = "read" /\ m.status = "ok") =>
            /\ DOMAIN m.val = Fields
            /\ [key |-> m.key, val |-> m.val, ver |-> m.ver] \in written

\* The store always holds exactly the latest applied write for each key
StoreReflectsLatest ==
    /\ \A r \in store : r.ver = verCtr[r.key] /\ r \in written
    /\ \A r \in store : \A w \in written : w.key = r.key => w.ver <= r.ver

\* No lost updates: a completed write is never overwritten except by a
\* later write, and every read linearized after a write completed observes
\* that write or a later one.
NoLostUpdates ==
    /\ \A k \in Keys : complVer[k] <= verCtr[k]
    /\ \A m \in AllObserved :
         (m.op = "read" /\ m.status # "none") => m.ver >= m.minVer

\* Integrity: the in-flight requests and responses are well formed
Integrity ==
    /\ \A c \in Clients :
         pc[c] = "idle" => ~\E m \in reqNet : m.client = c
    /\ \A m \in reqNet : m.seq = seq[m.client] /\ pc[m.client] = "waiting"

Safety ==
    /\ TypeOK
    /\ KeyUniqueness
    /\ CapacityBound
    /\ DomainConstraint
    /\ NoSentinelCreated
    /\ NoSentinelObserved
    /\ SentinelWritesRejected
    /\ NoTornReads
    /\ StoreReflectsLatest
    /\ NoLostUpdates
    /\ Integrity

-----------------------------------------------------------------------------
(*************************** LIVENESS PROPERTIES ***************************)

\* No operation invoked by a correct client is permanently blocked
NoPermanentBlocking ==
    \A c \in Clients \ Faulty : (pc[c] = "waiting") ~> (pc[c] = "idle")

\* Every request is eventually applied by the server
RequestsEventuallyServed ==
    \A c \in Clients :
        (\E m \in reqNet : m.client = c) ~> (\A m \in reqNet : m.client # c)

\* Completed updates eventually become (and remain) visible to readers
UpdatesEventuallyVisible ==
    \A k \in Keys, n \in 1..(Cardinality(Clients) * MaxOps) :
        (complVer[k] >= n) ~> (verCtr[k] >= n)

THEOREM Spec => []Safety
THEOREM Spec => NoPermanentBlocking /\ RequestsEventuallyServed /\ UpdatesEventuallyVisible
=============================================================================