---- MODULE SingleNodeReads ----
\* Single-node model extended with read-only transactions.
\* The base SingleNode behaviour (read-write transactions, execution,
\* responses and ledger branching) is included inline so that the module
\* is self-contained.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

ASSUME HistoryLimit \in Nat /\ ViewLimit \in Nat \ {0}

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* Event types of the external history
RwTxRequest  == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest  == "RoTxRequest"
RoTxResponse == "RoTxResponse"

\* Request identifiers are allocated sequentially
NextRequestId ==
    Cardinality({i \in DOMAIN history :
                    history[i].type \in {RwTxRequest, RoTxRequest}})

\* Current (latest) ledger branch
CurrentView == Len(ledgerBranches)

\* Transactions observed by a ledger branch
Observed(branch) == [seqnum \in DOMAIN branch |-> branch[seqnum].tx]

------------------------------------------------------------------------
\* Base SingleNode specification

Init ==
    /\ history = <<>>
    /\ ledgerBranches = <<<<>>>>

\* Submit a new read-write transaction
RwTxnRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction by appending it to the current branch
RwTxnExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A b \in DOMAIN ledgerBranches :
             \A s \in DOMAIN ledgerBranches[b] :
                ledgerBranches[b][s].tx # history[i].tx
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to a read-write transaction that has been executed
RwTxnResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E view \in DOMAIN ledgerBranches :
        \E seqnum \in DOMAIN ledgerBranches[view] :
            /\ \A k \in DOMAIN history :
                 ~ ( /\ history[k].type = RwTxResponse
                     /\ history[k].tx = ledgerBranches[view][seqnum].tx )
            /\ history' = Append(history,
                 [type     |-> RwTxResponse,
                  tx       |-> ledgerBranches[view][seqnum].tx,
                  observed |-> Observed(SubSeq(ledgerBranches[view], 1, seqnum)),
                  tx_id    |-> <<ledgerBranches[view][seqnum].view, seqnum>>])
    /\ UNCHANGED ledgerBranches

\* Start a new view whose ledger is a prefix of the current branch
TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in 0..Len(ledgerBranches[CurrentView]) :
         ledgerBranches' =
            Append(ledgerBranches, SubSeq(ledgerBranches[CurrentView], 1, i))
    /\ UNCHANGED history

NextSingleNodeAction ==
    \/ RwTxnRequestAction
    \/ RwTxnExecuteAction
    \/ RwTxnResponseAction
    \/ TruncateLedgerAction

SpecSingleNode == Init /\ [][NextSingleNodeAction]_vars

------------------------------------------------------------------------
\* Read-only transaction extension

\* Submit new read-only transaction
RoTxnRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Response to a read-only transaction request.
\* Assumes read-only transactions are always forwarded, and that the
\* read and the response happen in one atomic step.
RoTxnResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A k \in DOMAIN history :
             ~ ( /\ history[k].type = RoTxResponse
                 /\ history[k].tx = history[i].tx )
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(history,
                 [type     |-> RoTxResponse,
                  tx       |-> history[i].tx,
                  observed |-> Observed(ledgerBranches[view]),
                  tx_id    |-> <<ledgerBranches[view][Len(ledgerBranches[view])].view,
                                 Len(ledgerBranches[view])>>])
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxnRequestAction
    \/ RoTxnResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

Spec == SpecSingleNodeReads

------------------------------------------------------------------------
\* Safety invariants

\* Every response corresponds to an earlier request of the matching kind
ResponsesFollowRequestsInv ==
    \A k \in DOMAIN history :
        history[k].type = RoTxResponse =>
            \E i \in 1..(k-1) :
                /\ history[i].type = RoTxRequest
                /\ history[i].tx = history[k].tx

\* Each read-only request receives at most one response
AtMostOneRoResponseInv ==
    \A j, k \in DOMAIN history :
        ( /\ history[j].type = RoTxResponse
          /\ history[k].type = RoTxResponse
          /\ history[j].tx = history[k].tx ) => j = k

\* The history never exceeds its bound
HistoryBoundInv == Len(history) <= HistoryLimit

====