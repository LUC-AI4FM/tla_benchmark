---------------------------- MODULE MCMultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ---------------------------------------------------------------------------
\* Inlined MultiNode base specification (the module being wrapped).
\* ---------------------------------------------------------------------------

CONSTANTS
    HistoryLimit    \* bound on the length of the client-observed history

VARIABLES
    history,         \* sequence of client-observed events
    ledgerBranches,  \* ledgerBranches[v] is the ledger as seen in view v
    commitSeqNum     \* highest committed sequence number in the latest branch

vars == <<history, ledgerBranches, commitSeqNum>>

RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

Event(t, tx, v, s) == [type |-> t, tx |-> tx, view |-> v, seqnum |-> s]

Views == DOMAIN ledgerBranches

LatestView == Len(ledgerBranches)

LatestLedger == ledgerBranches[LatestView]

RequestIndices ==
    {i \in DOMAIN history : history[i].type = RwTxRequest}

NumRequests == Cardinality(RequestIndices)

RequestedTxs == {history[i].tx : i \in RequestIndices}

TxsInLedger(l) == {l[i].tx : i \in DOMAIN l}

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

\* A client submits a new read-write transaction request.
ClientSendRequestAction ==
    /\ history' = Append(history, Event(RwTxRequest, NumRequests + 1, 0, 0))
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* A (possibly stale) leader in view v executes a pending request,
\* appending it to its branch and replying to the client.
ExecuteRequestAction(v) ==
    \E t \in RequestedTxs \ TxsInLedger(ledgerBranches[v]) :
        /\ ledgerBranches' =
               [ledgerBranches EXCEPT ![v] = Append(@, [view |-> v, tx |-> t])]
        /\ history' =
               Append(history,
                      Event(RwTxResponse, t, v, Len(ledgerBranches[v]) + 1))
        /\ UNCHANGED commitSeqNum

ExecuteRequestAnyAction ==
    \E v \in Views : ExecuteRequestAction(v)

\* A view change: a new branch starts from the committed prefix of the
\* latest branch.
AppendBranchAction ==
    /\ ledgerBranches' =
           Append(ledgerBranches, SubSeq(LatestLedger, 1, commitSeqNum))
    /\ UNCHANGED <<history, commitSeqNum>>

\* The leader of the latest view commits the next entry and the client
\* learns of its committed status.
CommitAction ==
    /\ commitSeqNum < Len(LatestLedger)
    /\ commitSeqNum' = commitSeqNum + 1
    /\ history' =
           Append(history,
                  Event(TxStatusReceived,
                        LatestLedger[commitSeqNum + 1].tx,
                        LatestLedger[commitSeqNum + 1].view,
                        commitSeqNum + 1))
    /\ UNCHANGED ledgerBranches

Next ==
    \/ ClientSendRequestAction
    \/ ExecuteRequestAnyAction
    \/ AppendBranchAction
    \/ CommitAction

Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Model-checking wrapper with an explicit bound on view changes.
\* ---------------------------------------------------------------------------

CONSTANT ViewLimit

ASSUME ViewLimit \in Nat \ {0}
ASSUME HistoryLimit \in Nat

\* Limit the number of view changes
MCAppendBranchAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ AppendBranchAction

\* Limit the length of the history (and thus the number of requests)
MCClientSendRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ ClientSendRequestAction

MCExecuteRequestAnyAction ==
    /\ Len(history) < HistoryLimit
    /\ ExecuteRequestAnyAction

MCCommitAction ==
    /\ Len(history) < HistoryLimit
    /\ CommitAction

MCNextMultiNodeAction ==
    \/ MCClientSendRequestAction
    \/ MCExecuteRequestAnyAction
    \/ MCAppendBranchAction
    \/ MCCommitAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

\* ---------------------------------------------------------------------------
\* Safety invariants
\* ---------------------------------------------------------------------------

TypeOK ==
    /\ history \in Seq([type   : {RwTxRequest, RwTxResponse, TxStatusReceived},
                        tx     : Nat,
                        view   : Nat,
                        seqnum : Nat])
    /\ ledgerBranches \in Seq(Seq([view : Nat \ {0}, tx : Nat \ {0}]))
    /\ Len(ledgerBranches) >= 1
    /\ commitSeqNum \in 0..Len(LatestLedger)

\* Bounds used for model checking are respected
BoundsInv ==
    /\ Len(ledgerBranches) <= ViewLimit
    /\ Len(history) <= HistoryLimit

\* Every response refers to a previously requested transaction
ResponsesMatchRequestsInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = history[i].tx

\* Once committed, a transaction stays at its position in the latest branch
CommittedTxsPersistInv ==
    \A i \in DOMAIN history :
        history[i].type = TxStatusReceived =>
            /\ history[i].seqnum <= commitSeqNum
            /\ LatestLedger[history[i].seqnum].tx = history[i].tx
            /\ LatestLedger[history[i].seqnum].view = history[i].view

\* No two commit notifications disagree on the transaction at a sequence number
UniqueCommitInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[j].type = TxStatusReceived
          /\ history[i].seqnum = history[j].seqnum )
        => history[i].tx = history[j].tx

\* Each branch contains each transaction at most once
NoDuplicatesInv ==
    \A v \in Views :
        \A a, b \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][a].tx = ledgerBranches[v][b].tx => a = b

=============================================================================