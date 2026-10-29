------------------------- MODULE SingleNodeReadOnlyTxn -------------------------
(***************************************************************************)
(* A single-node key/value database that supports regular reads and       *)
(* writes, plus read-only transactions. A read-only transaction is split  *)
(* into a request step and a response step. The response returns a       *)
(* consistent snapshot of the whole database.                             *)
(*                                                                         *)
(* The history of operations is recorded so that consistency properties   *)
(* (linearizability and snapshot consistency) can be checked.             *)
(*                                                                         *)
(* Bounds for model checking:                                              *)
(*  - Operations that start new work (writes, reads, read-only requests)  *)
(*    are enabled only while Len(history) < MaxHistory.                   *)
(*  - A read-only response is always allowed, because each client has at  *)
(*    most one outstanding request. This keeps liveness satisfiable and   *)
(*    limits the history length to MaxHistory + Cardinality(Clients).     *)
(*  - Keys, Values and Clients are finite sets.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Keys,          \* finite set of keys
    Values,        \* finite set of values that can be written
    Clients,       \* finite set of clients
    NoValue,       \* value of a key that has never been written
    MaxHistory     \* bound on the history length for new operations

ASSUME NoValue \notin Values
ASSUME MaxHistory \in Nat
ASSUME IsFiniteSet(Keys) /\ IsFiniteSet(Values) /\ IsFiniteSet(Clients)

VARIABLES
    kv,          \* current database state: [Keys -> Values \cup {NoValue}]
    version,     \* number of committed writes (logical commit timestamp)
    kvLog,       \* kvLog[v+1] = database state at version v (for checking)
    history,     \* sequence of operation records
    roState,     \* [Clients -> {"idle", "pending"}]
    roReqVer     \* [Clients -> Nat]: version when the pending RO request started

vars == <<kv, version, kvLog, history, roState, roReqVer>>

-----------------------------------------------------------------------------
(* Foundational definitions from the base single-node model *)

Val     == Values \cup {NoValue}
KVState == [Keys -> Val]
InitKV  == [k \in Keys |-> NoValue]

WriteRec  == [type : {"write"}, client : Clients, key : Keys,
              value : Values, version : Nat]
ReadRec   == [type : {"read"}, client : Clients, key : Keys,
              value : Val, version : Nat]
RORequest == [type : {"ro_req"}, client : Clients, version : Nat]
ROResponse == [type : {"ro_resp"}, client : Clients, reqVersion : Nat,
               version : Nat, snapshot : KVState]

HistoryRec == WriteRec \cup ReadRec \cup RORequest \cup ROResponse

CanAct == Len(history) < MaxHistory

TypeOK ==
    /\ kv \in KVState
    /\ version \in 0..MaxHistory
    /\ kvLog \in Seq(KVState)
    /\ Len(kvLog) = version + 1
    /\ history \in Seq(HistoryRec)
    /\ Len(history) <= MaxHistory + Cardinality(Clients)
    /\ roState \in [Clients -> {"idle", "pending"}]
    /\ roReqVer \in [Clients -> 0..MaxHistory]

-----------------------------------------------------------------------------
Init ==
    /\ kv = InitKV
    /\ version = 0
    /\ kvLog = <<InitKV>>
    /\ history = <<>>
    /\ roState = [c \in Clients |-> "idle"]
    /\ roReqVer = [c \in Clients |-> 0]

(* ---------------- Base single-node operations ---------------- *)

Write(c, k, v) ==
    /\ CanAct
    /\ LET newKV == [kv EXCEPT ![k] = v]
       IN /\ kv' = newKV
          /\ version' = version + 1
          /\ kvLog' = Append(kvLog, newKV)
          /\ history' = Append(history,
                [type |-> "write", client |-> c, key |-> k,
                 value |-> v, version |-> version + 1])
    /\ UNCHANGED <<roState, roReqVer>>

Read(c, k) ==
    /\ CanAct
    /\ history' = Append(history,
            [type |-> "read", client |-> c, key |-> k,
             value |-> kv[k], version |-> version])
    /\ UNCHANGED <<kv, version, kvLog, roState, roReqVer>>

BaseNext ==
    \/ \E c \in Clients, k \in Keys, v \in Values : Write(c, k, v)
    \/ \E c \in Clients, k \in Keys : Read(c, k)

(* ---------------- Read-only transactions ---------------- *)

ROStart(c) ==
    /\ CanAct
    /\ roState[c] = "idle"
    /\ roState' = [roState EXCEPT ![c] = "pending"]
    /\ roReqVer' = [roReqVer EXCEPT ![c] = version]
    /\ history' = Append(history,
            [type |-> "ro_req", client |-> c, version |-> version])
    /\ UNCHANGED <<kv, version, kvLog>>

ROReply(c) ==
    /\ roState[c] = "pending"
    /\ roState' = [roState EXCEPT ![c] = "idle"]
    /\ history' = Append(history,
            [type |-> "ro_resp", client |-> c, reqVersion |-> roReqVer[c],
             version |-> version, snapshot |-> kv])
    /\ UNCHANGED <<kv, version, kvLog, roReqVer>>

ROActions ==
    \/ \E c \in Clients : ROStart(c)
    \/ \E c \in Clients : ROReply(c)

Next == BaseNext \/ ROActions

Fairness == \A c \in Clients : WF_vars(ROReply(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* ---------------- Safety properties ---------------- *)

\* The database always matches the latest logged state.
StateMatchesLog == kv = kvLog[version + 1]

\* Each write in the history produces exactly the logged state at its version.
WritesConsistent ==
    \A i \in 1..Len(history) :
        LET e == history[i] IN
        e.type = "write" =>
            /\ e.version \in 1..version
            /\ kvLog[e.version + 1] = [kvLog[e.version] EXCEPT ![e.key] = e.value]

\* Each single-key read returns the value at its linearization point.
ReadsConsistent ==
    \A i \in 1..Len(history) :
        LET e == history[i] IN
        e.type = "read" =>
            /\ e.version \in 0..version
            /\ e.value = kvLog[e.version + 1][e.key]

\* Consistency of reads: each read-only transaction sees a consistent
\* committed snapshot. The snapshot is linearized between its request and
\* its response.
ROSnapshotConsistent ==
    \A i \in 1..Len(history) :
        LET e == history[i] IN
        e.type = "ro_resp" =>
            /\ e.reqVersion <= e.version
            /\ e.version <= version
            /\ e.snapshot = kvLog[e.version + 1]

\* Versions in the history never decrease (real-time order is respected).
HistoryMonotonic ==
    \A i, j \in 1..Len(history) :
        i < j => history[i].version <= history[j].version

\* Every response matches an earlier request from the same client.
ROWellFormed ==
    \A i \in 1..Len(history) :
        LET e == history[i] IN
        e.type = "ro_resp" =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = "ro_req"
                /\ history[j].client = e.client
                /\ history[j].version = e.reqVersion

\* At most one outstanding read-only request per client.
ROBounded ==
    \A c \in Clients :
        Cardinality({i \in 1..Len(history) :
                        history[i].type = "ro_req" /\ history[i].client = c})
        - Cardinality({i \in 1..Len(history) :
                        history[i].type = "ro_resp" /\ history[i].client = c})
        \in IF roState[c] = "pending" THEN {1} ELSE {0}

Safety ==
    /\ TypeOK
    /\ StateMatchesLog
    /\ WritesConsistent
    /\ ReadsConsistent
    /\ ROSnapshotConsistent
    /\ HistoryMonotonic
    /\ ROWellFormed
    /\ ROBounded

\* Non-interference: read-only transaction steps never modify database state.
NonInterference ==
    [][ROActions => UNCHANGED <<kv, version, kvLog>>]_vars

\* The committed state only evolves by appending versions.
LogAppendOnly ==
    [][ /\ version' >= version
        /\ SubSeq(kvLog', 1, Len(kvLog)) = kvLog ]_vars

(* ---------------- Liveness properties ---------------- *)

\* Every pending read-only transaction eventually receives a response.
ROEventuallyAnswered ==
    \A c \in Clients : (roState[c] = "pending") ~> (roState[c] = "idle")

THEOREM Spec => []Safety
THEOREM Spec => NonInterference /\ LogAppendOnly
THEOREM Spec => ROEventuallyAnswered
=============================================================================