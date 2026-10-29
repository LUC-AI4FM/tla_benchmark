---------------------------- MODULE SingleNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxs,      \* identifiers of read-write transactions
    RoTxs,      \* identifiers of read-only transactions
    MaxView     \* bound on the number of views (ledger branches)

ASSUME RwTxs \cap RoTxs = {}
ASSUME RwTxs # {}
ASSUME MaxView \in Nat \ {0}

\* Event types recorded in the history
RwTxRequest  == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest  == "RoTxRequest"
RoTxResponse == "RoTxResponse"

VARIABLES
    history,         \* sequence of all requests and responses
    ledgerBranches   \* ledgerBranches[v] is the ledger as seen in view v

vars == <<history, ledgerBranches>>

------------------------------------------------------------------------------
\* Helpers

Range(f) == {f[i] : i \in DOMAIN f}

TxIds(s) == [k \in 1..Len(s) |-> s[k].tx]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

LastBranch == ledgerBranches[Len(ledgerBranches)]

CurrentView == Len(ledgerBranches)

Requested(type, tx) ==
    \E i \in DOMAIN history : history[i].type = type /\ history[i].tx = tx

Responded(type, tx) ==
    \E i \in DOMAIN history : history[i].type = type /\ history[i].tx = tx

InSomeBranch(tx) ==
    \E v \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[v] : ledgerBranches[v][k].tx = tx

TxIdType == (1..MaxView) \X Nat

RequestType ==
    [type : {RwTxRequest}, tx : RwTxs] \cup [type : {RoTxRequest}, tx : RoTxs]

ResponseType ==
    [type : {RwTxResponse}, tx : RwTxs, observed : Seq(RwTxs), tx_id : TxIdType]
    \cup
    [type : {RoTxResponse}, tx : RoTxs, observed : Seq(RwTxs), tx_id : TxIdType]

------------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

------------------------------------------------------------------------------
\* Read-write transactions (existing single-node behaviour)

\* A client submits a new read-write transaction
RwTxRequestAction(tx) ==
    /\ ~Requested(RwTxRequest, tx)
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
    /\ UNCHANGED ledgerBranches

\* The node executes a requested read-write transaction, appending it to the ledger
RwTxExecute(tx) ==
    /\ Requested(RwTxRequest, tx)
    /\ ~InSomeBranch(tx)
    /\ ledgerBranches' =
         [ledgerBranches EXCEPT ![CurrentView] =
             Append(@, [view |-> CurrentView, tx |-> tx])]
    /\ UNCHANGED history

\* The node responds to an executed read-write transaction
RwTxResponseAction(tx) ==
    /\ Requested(RwTxRequest, tx)
    /\ ~Responded(RwTxResponse, tx)
    /\ \E v \in DOMAIN ledgerBranches :
         \E i \in DOMAIN ledgerBranches[v] :
            /\ ledgerBranches[v][i].tx = tx
            /\ history' = Append(history,
                  [type     |-> RwTxResponse,
                   tx       |-> tx,
                   observed |-> TxIds(SubSeq(ledgerBranches[v], 1, i)),
                   tx_id    |-> <<ledgerBranches[v][i].view, i>>])
    /\ UNCHANGED ledgerBranches

\* A view change: a new branch is started from a prefix of the current branch
NewView ==
    /\ CurrentView < MaxView
    /\ \E i \in 0..Len(LastBranch) :
         ledgerBranches' = Append(ledgerBranches, SubSeq(LastBranch, 1, i))
    /\ UNCHANGED history

------------------------------------------------------------------------------
\* Read-only transactions (new)

\* A client submits a read-only transaction; it is always forwarded
RoTxRequestAction(tx) ==
    /\ ~Requested(RoTxRequest, tx)
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> tx])
    /\ UNCHANGED ledgerBranches

\* The node atomically reads a non-empty branch and responds
RoTxResponseAction(tx) ==
    /\ Requested(RoTxRequest, tx)
    /\ ~Responded(RoTxResponse, tx)
    /\ \E v \in DOMAIN ledgerBranches :
         /\ Len(ledgerBranches[v]) > 0
         /\ history' = Append(history,
               [type     |-> RoTxResponse,
                tx       |-> tx,
                observed |-> TxIds(ledgerBranches[v]),
                tx_id    |-> <<ledgerBranches[v][Len(ledgerBranches[v])].view,
                               Len(ledgerBranches[v])>>])
    /\ UNCHANGED ledgerBranches

------------------------------------------------------------------------------
\* Next-state relation and specification

Next ==
    \/ \E tx \in RwTxs : RwTxRequestAction(tx)
    \/ \E tx \in RwTxs : RwTxExecute(tx)
    \/ \E tx \in RwTxs : RwTxResponseAction(tx)
    \/ NewView
    \/ \E tx \in RoTxs : RoTxRequestAction(tx)
    \/ \E tx \in RoTxs : RoTxResponseAction(tx)

Fairness ==
    /\ \A tx \in RwTxs : WF_vars(RwTxRequestAction(tx))
    /\ \A tx \in RwTxs : WF_vars(RwTxExecute(tx))
    /\ \A tx \in RwTxs : WF_vars(RwTxResponseAction(tx))
    /\ \A tx \in RoTxs : WF_vars(RoTxResponseAction(tx))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ history \in Seq(RequestType \cup ResponseType)
    /\ ledgerBranches \in Seq(Seq([view : 1..MaxView, tx : RwTxs]))
    /\ Len(ledgerBranches) >= 1

\* Each transaction is requested at most once
UniqueRequests ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in {RwTxRequest, RoTxRequest}
        /\ history[j].type = history[i].type
        /\ history[i].tx = history[j].tx
        => i = j

\* Each transaction request receives at most one response
AtMostOneResponse ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ history[j].type = history[i].type
        /\ history[i].tx = history[j].tx
        => i = j

\* Every response references an earlier request of the matching kind
ResponsesMatchRequests ==
    \A i \in DOMAIN history :
        /\ (history[i].type = RwTxResponse =>
              \E j \in 1..(i-1) : history[j].type = RwTxRequest
                                  /\ history[j].tx = history[i].tx)
        /\ (history[i].type = RoTxResponse =>
              \E j \in 1..(i-1) : history[j].type = RoTxRequest
                                  /\ history[j].tx = history[i].tx)

\* Read-only responses observe a real ledger state: a prefix of some branch,
\* and the tx_id identifies exactly the view and position that was read
RoConsistentReads ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            LET r == history[i] IN
            /\ Len(r.observed) = r.tx_id[2]
            /\ r.tx_id[2] > 0
            /\ \E v \in DOMAIN ledgerBranches :
                 /\ Len(ledgerBranches[v]) >= r.tx_id[2]
                 /\ r.observed = TxIds(SubSeq(ledgerBranches[v], 1, r.tx_id[2]))
                 /\ ledgerBranches[v][r.tx_id[2]].view = r.tx_id[1]

\* Read-write responses observe a prefix ending in the transaction itself
RwConsistentResponses ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            LET r == history[i] IN
            /\ Len(r.observed) = r.tx_id[2]
            /\ r.tx_id[2] > 0
            /\ r.observed[r.tx_id[2]] = r.tx
            /\ \E v \in DOMAIN ledgerBranches :
                 /\ Len(ledgerBranches[v]) >= r.tx_id[2]
                 /\ r.observed = TxIds(SubSeq(ledgerBranches[v], 1, r.tx_id[2]))
                 /\ ledgerBranches[v][r.tx_id[2]].view = r.tx_id[1]

\* Ledger structure: each branch is a prefix-extension of an earlier branch
\* and entry views never exceed the branch's view
LedgerWellFormed ==
    \A v \in DOMAIN ledgerBranches :
        \A k \in DOMAIN ledgerBranches[v] :
            /\ ledgerBranches[v][k].view <= v
            /\ (k > 1 => ledgerBranches[v][k-1].view <= ledgerBranches[v][k].view)

\* A transaction appears at most once in any branch
NoDuplicateLedgerEntries ==
    \A v \in DOMAIN ledgerBranches :
        \A k1, k2 \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][k1].tx = ledgerBranches[v][k2].tx => k1 = k2

Safety ==
    /\ TypeOK
    /\ UniqueRequests
    /\ AtMostOneResponse
    /\ ResponsesMatchRequests
    /\ RoConsistentReads
    /\ RwConsistentResponses
    /\ LedgerWellFormed
    /\ NoDuplicateLedgerEntries

------------------------------------------------------------------------------
\* Liveness properties

\* Every read-only request eventually receives a response
RoTxEventuallyResponds ==
    \A tx \in RoTxs :
        Requested(RoTxRequest, tx) ~> Responded(RoTxResponse, tx)

\* Every read-write request eventually receives a response
RwTxEventuallyResponds ==
    \A tx \in RwTxs :
        Requested(RwTxRequest, tx) ~> Responded(RwTxResponse, tx)

Liveness == RoTxEventuallyResponds /\ RwTxEventuallyResponds

THEOREM Spec => []Safety
THEOREM Spec => Liveness
================================================================================