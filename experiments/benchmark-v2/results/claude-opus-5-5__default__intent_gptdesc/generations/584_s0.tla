---------------------------- MODULE SingleNodeTxService ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxs,        \* identifiers of read-write transaction requests
    RoTxs,        \* identifiers of read-only transaction requests
    MaxBranches   \* bound on the number of ledger branches (rollbacks) for model checking

ASSUME RwTxs \cap RoTxs = {}
ASSUME MaxBranches \in Nat \ {0}

\* Event types recorded in the history
RwTxRequest  == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest  == "RoTxRequest"
RoTxResponse == "RoTxResponse"

RequestTypes  == {RwTxRequest, RoTxRequest}
ResponseTypes == {RwTxResponse, RoTxResponse}

RequestOf(rtype) == IF rtype = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

VARIABLES
    history,         \* sequence of request/response events observed by the node
    ledgerBranches   \* sequence of ledger branches; each branch is a sequence of committed RW txs

vars == <<history, ledgerBranches>>

-----------------------------------------------------------------------------
\* Helpers

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

NoDuplicates(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

CurrentBranchIdx == Len(ledgerBranches)
CurrentBranch    == ledgerBranches[CurrentBranchIdx]

Requested(rtype, t) ==
    \E i \in DOMAIN history : history[i].type = rtype /\ history[i].tx = t

Responded(rtype, t) ==
    \E i \in DOMAIN history : history[i].type = rtype /\ history[i].tx = t

\* A valid snapshot exists when the current branch has at least one committed transaction
ValidSnapshotExists == Len(CurrentBranch) > 0

\* A snapshot identifier (branch index, prefix length) is valid
ValidTxId(id) ==
    /\ id[1] \in 1..Len(ledgerBranches)
    /\ id[2] \in 1..Len(ledgerBranches[id[1]])

RequestEvents ==
    [type : RequestTypes, tx : RwTxs \cup RoTxs]

ResponseEvents ==
    [type : ResponseTypes, tx : RwTxs \cup RoTxs,
     observed : Seq(RwTxs), tx_id : (Nat \ {0}) \X Nat]

Events == RequestEvents \cup ResponseEvents

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = << >>
    /\ ledgerBranches = << << >> >>

-----------------------------------------------------------------------------
\* Actions

\* Node receives a new read-write transaction request
ReceiveRwTx(t) ==
    /\ ~Requested(RwTxRequest, t)
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> t])
    /\ UNCHANGED ledgerBranches

\* Node executes and commits a read-write transaction, mutating the ledger,
\* and responds with the observed ledger prefix and the snapshot identifier
ExecuteRwTx(t) ==
    /\ Requested(RwTxRequest, t)
    /\ ~Responded(RwTxResponse, t)
    /\ \A i \in DOMAIN CurrentBranch : CurrentBranch[i] # t
    /\ LET nb == Append(CurrentBranch, t)
       IN /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentBranchIdx] = nb]
          /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> t,
                 observed |-> nb,
                 tx_id    |-> <<CurrentBranchIdx, Len(nb)>>])

\* Node receives a new read-only transaction request
ReceiveRoTx(t) ==
    /\ ~Requested(RoTxRequest, t)
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> t])
    /\ UNCHANGED ledgerBranches

\* Node responds (exactly once) to a previously received read-only request by
\* reading a prefix snapshot of the current ledger branch, without modifying it
RespondRoTx(t) ==
    /\ Requested(RoTxRequest, t)
    /\ ~Responded(RoTxResponse, t)
    /\ ValidSnapshotExists
    /\ \E i \in 1..Len(CurrentBranch) :
          history' = Append(history,
                [type     |-> RoTxResponse,
                 tx       |-> t,
                 observed |-> SubSeq(CurrentBranch, 1, i),
                 tx_id    |-> <<CurrentBranchIdx, i>>])
    /\ UNCHANGED ledgerBranches

\* Ledger rollback: a new branch is started from a prefix of the current branch
TruncateLedger ==
    /\ Len(ledgerBranches) < MaxBranches
    /\ \E k \in 0..Len(CurrentBranch) :
          ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, k))
    /\ UNCHANGED history

Next ==
    \/ \E t \in RwTxs : ReceiveRwTx(t)
    \/ \E t \in RwTxs : ExecuteRwTx(t)
    \/ \E t \in RoTxs : ReceiveRoTx(t)
    \/ \E t \in RoTxs : RespondRoTx(t)
    \/ TruncateLedger

Fairness ==
    /\ \A t \in RwTxs : WF_vars(ExecuteRwTx(t))
    /\ \A t \in RoTxs : SF_vars(RespondRoTx(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ history \in Seq(Events)
    /\ ledgerBranches \in Seq(Seq(RwTxs))
    /\ Len(ledgerBranches) >= 1

\* Responses appear after the request they answer, and reference its identifier
HistoryOrdered ==
    \A i \in DOMAIN history :
        history[i].type \in ResponseTypes =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = RequestOf(history[i].type)
                /\ history[j].tx = history[i].tx

\* Each request identifier is received at most once
NoDuplicateRequests ==
    \A i, j \in DOMAIN history :
        (i # j /\ history[i].type \in RequestTypes /\ history[j].type = history[i].type)
            => history[i].tx # history[j].tx

\* Each request is answered at most once
NoDuplicateResponses ==
    \A i, j \in DOMAIN history :
        (i # j /\ history[i].type \in ResponseTypes /\ history[j].type = history[i].type)
            => history[i].tx # history[j].tx

\* Read-only responses reflect a consistent prefix of an existing ledger branch
RoResponsesConsistent ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            /\ ValidTxId(history[i].tx_id)
            /\ history[i].observed =
                 SubSeq(ledgerBranches[history[i].tx_id[1]], 1, history[i].tx_id[2])

\* Read-write responses reflect the ledger prefix ending in their own commit
RwResponsesConsistent ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            /\ ValidTxId(history[i].tx_id)
            /\ ledgerBranches[history[i].tx_id[1]][history[i].tx_id[2]] = history[i].tx
            /\ history[i].observed =
                 SubSeq(ledgerBranches[history[i].tx_id[1]], 1, history[i].tx_id[2])

\* Ledger branch structure and snapshot indices are well formed
LedgerBranchesWellFormed ==
    /\ Len(ledgerBranches) \in 1..MaxBranches
    /\ \A b \in DOMAIN ledgerBranches :
          /\ NoDuplicates(ledgerBranches[b])
          /\ \A k \in DOMAIN ledgerBranches[b] :
                Requested(RwTxRequest, ledgerBranches[b][k])

Invariants ==
    /\ TypeOK
    /\ HistoryOrdered
    /\ NoDuplicateRequests
    /\ NoDuplicateResponses
    /\ RoResponsesConsistent
    /\ RwResponsesConsistent
    /\ LedgerBranchesWellFormed

-----------------------------------------------------------------------------
\* Action (temporal safety) properties

\* The history is append-only
HistoryAppendOnly == [][IsPrefix(history, history')]_vars

\* The ledger evolves only through valid commits or branch creation
LedgerEvolvesOnlyByCommit ==
    [][ledgerBranches' # ledgerBranches =>
         \/ \E t \in RwTxs : ExecuteRwTx(t)
         \/ TruncateLedger]_vars

\* Existing branches are only ever extended, never rewritten
BranchesOnlyExtended ==
    [][ /\ Len(ledgerBranches) <= Len(ledgerBranches')
        /\ \A b \in DOMAIN ledgerBranches :
              IsPrefix(ledgerBranches[b], ledgerBranches'[b]) ]_vars

\* Read-only responses never change the ledger (no interference with commits)
RoResponsesDoNotMutateLedger ==
    [][(\E t \in RoTxs : RespondRoTx(t)) => UNCHANGED ledgerBranches]_vars

\* Read-only responses reflect a prefix of the current branch at response time
RoResponseReflectsLedgerAtResponse ==
    [][(\E t \in RoTxs : RespondRoTx(t)) =>
         LET r == history'[Len(history')]
         IN  /\ r.tx_id[1] = CurrentBranchIdx
             /\ IsPrefix(r.observed, CurrentBranch)]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* If valid snapshots keep existing, every read-only request is eventually answered
RoTxEventuallyAnswered ==
    \A t \in RoTxs :
        ([]<>ValidSnapshotExists) =>
            (Requested(RoTxRequest, t) ~> Responded(RoTxResponse, t))

\* A pending read-only request with a valid snapshot is eventually answered,
\* unless the snapshot disappears through a rollback
RoTxAnsweredWhenSnapshotValid ==
    \A t \in RoTxs :
        (Requested(RoTxRequest, t) /\ ValidSnapshotExists)
            ~> (Responded(RoTxResponse, t) \/ ~ValidSnapshotExists)

=============================================================================