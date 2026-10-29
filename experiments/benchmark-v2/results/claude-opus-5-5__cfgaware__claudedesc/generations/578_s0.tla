---------------------------- MODULE MCMultiNodeReads ----------------------------
(***************************************************************************)
(* Bounded model-checking spec for a multi-node distributed system that    *)
(* supports both read-write and read-only transactions.  Self-contained:   *)
(* the multi-node machinery (ledger branches per view, commit, view        *)
(* changes with truncation, read-write requests, responses and statuses)   *)
(* and the single-node read machinery (read-only requests and responses)   *)
(* are defined inline.                                                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus

\* Bounds for model checking
HistoryLimit == 6
ViewLimit == 3
FirstBranch == 1

VARIABLES history, ledgerBranches, commitSeqNum

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
\* Helpers

Range(s) == {s[k] : k \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

CurrentView == Len(ledgerBranches)

Latest == ledgerBranches[CurrentView]

ExecutedTxs ==
    UNION { {ledgerBranches[v][k].tx : k \in DOMAIN ledgerBranches[v]} :
            v \in DOMAIN ledgerBranches }

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in {FirstBranch} |-> <<>>]
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
\* Multi-node actions (read-write transactions, commit, view changes)

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history:
        /\ history[i].type = RwTxRequest
        /\ history[i].tx \notin ExecutedTxs
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E v \in DOMAIN ledgerBranches:
        \E k \in DOMAIN ledgerBranches[v]:
            /\ ledgerBranches[v][k].view = v
            /\ ~ \E j \in DOMAIN history:
                    /\ history[j].type = RwTxResponse
                    /\ history[j].tx = ledgerBranches[v][k].tx
            /\ history' = Append(history,
                  [type |-> RwTxResponse,
                   tx |-> ledgerBranches[v][k].tx,
                   observed |-> [x \in 1..k |-> ledgerBranches[v][x].tx],
                   tx_id |-> <<v, k>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

IsCommittedId(id) ==
    /\ id[2] <= commitSeqNum
    /\ id[2] <= Len(Latest)
    /\ Latest[id[2]].view = id[1]

IsInvalidId(id) ==
    /\ CurrentView > id[1]
    /\ \/ id[2] > Len(Latest)
       \/ Latest[id[2]].view # id[1]

HasStatus(id) ==
    \E j \in DOMAIN history:
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx_id = id

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history:
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ ~ HasStatus(history[i].tx_id)
        /\ IsCommittedId(history[i].tx_id)
        /\ history' = Append(history,
              [type |-> TxStatusReceived,
               tx_id |-> history[i].tx_id,
               status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history:
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ ~ HasStatus(history[i].tx_id)
        /\ IsInvalidId(history[i].tx_id)
        /\ history' = Append(history,
              [type |-> TxStatusReceived,
               tx_id |-> history[i].tx_id,
               status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

IncreaseCommitAction ==
    /\ commitSeqNum < Len(Latest)
    /\ \E n \in (commitSeqNum + 1)..Len(Latest): commitSeqNum' = n
    /\ UNCHANGED <<history, ledgerBranches>>

TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E n \in commitSeqNum..Len(Latest):
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, n))
    /\ UNCHANGED <<history, commitSeqNum>>

NextMultiNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ IncreaseCommitAction
    \/ TruncateLedgerAction

-----------------------------------------------------------------------------
\* Read-only transaction actions

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history:
        /\ history[i].type = RoTxRequest
        /\ ~ \E j \in DOMAIN history:
                /\ history[j].type = RoTxResponse
                /\ history[j].tx = history[i].tx
        /\ \E v \in DOMAIN ledgerBranches:
            LET b == ledgerBranches[v] IN
            /\ Len(b) > 0
            /\ history' = Append(history,
                  [type |-> RoTxResponse,
                   tx |-> history[i].tx,
                   observed |-> [x \in 1..Len(b) |-> b[x].tx],
                   tx_id |-> <<b[Len(b)].view, Len(b)>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
NextMultiNodeReads ==
    \/ NextMultiNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

MCSpecMultiNodeReads == Init /\ [][NextMultiNodeReads]_vars

-----------------------------------------------------------------------------
\* Derived sets for invariants

RwResps == {i \in DOMAIN history : history[i].type = RwTxResponse}

Resps == {i \in DOMAIN history : history[i].type \in {RwTxResponse, RoTxResponse}}

Requests == {i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}}

StatusIdx(s) ==
    {i \in DOMAIN history : history[i].type = TxStatusReceived /\ history[i].status = s}

CommittedIds == {history[i].tx_id : i \in StatusIdx(CommittedStatus)}

InvalidIds == {history[i].tx_id : i \in StatusIdx(InvalidStatus)}

CommittedRwResps == {i \in RwResps : history[i].tx_id \in CommittedIds}

CommittedResps == {i \in Resps : history[i].tx_id \in CommittedIds}

InvalidRwResps == {i \in RwResps : history[i].tx_id \in InvalidIds}

MatchingRequest(t) == IF t = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

-----------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    /\ \A i \in Resps:
        \E k \in DOMAIN history:
            /\ k < i
            /\ history[k].type = MatchingRequest(history[i].type)
            /\ history[k].tx = history[i].tx
    /\ \A i \in DOMAIN history:
        history[i].type = TxStatusReceived =>
            \E k \in Resps: k < i /\ history[k].tx_id = history[i].tx_id

AllCommittedObservedInv ==
    \A i, j \in CommittedRwResps:
        history[i].tx_id[2] <= history[j].tx_id[2] =>
            history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in Resps:
        \A t \in Range(history[i].observed):
            \E k \in DOMAIN history:
                /\ k < i
                /\ history[k].type = RwTxRequest
                /\ history[k].tx = t

UniqueTxsInv ==
    \A i, j \in RwResps: history[i].tx = history[j].tx => i = j

SameObservationsInv ==
    \A i, j \in Resps:
        history[i].tx_id = history[j].tx_id =>
            history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in RwResps: history[i].tx_id = history[j].tx_id => i = j

UniqueTxRequestsInv ==
    \A i, j \in Requests: history[i].tx = history[j].tx => i = j

UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRwResps:
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

CommittedOrInvalidStrongInv ==
    /\ CommittedIds \cap InvalidIds = {}
    /\ \A id \in CommittedIds: IsCommittedId(id)
    /\ \A id \in InvalidIds: ~ IsCommittedId(id) /\ IsInvalidId(id)

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResps:
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwResps:
        \A j \in CommittedResps:
            history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in Resps:
        \A a, b \in DOMAIN history[i].observed:
            a # b => history[i].observed[a] # history[i].observed[b]

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwResps:
        (\E k \in DOMAIN history:
            /\ k > i
            /\ history[k].type = RwTxRequest
            /\ history[k].tx = history[j].tx)
        => history[i].tx_id[2] < history[j].tx_id[2]

=============================================================================