---------------------------- MODULE MCSingleNodeReads ----------------------------
(***************************************************************************)
(* Bounded model-checking version of a single-node system handling both  *)
(* read-write (Rw) and read-only (Ro) transactions. It combines the       *)
(* single-node behaviour (Rw requests, execution, responses, commit and   *)
(* status notifications) with read-only transaction requests and          *)
(* responses. Every action that extends the history is enabled only      *)
(* while Len(history) < HistoryLimit.                                     *)
(*                                                                         *)
(* Intended configuration:                                                 *)
(*   HistoryLimit = 7, a single ledger branch,                            *)
(*   RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse,                *)
(*   TxStatusReceived, CommittedStatus, InvalidStatus as model values,    *)
(*   CHECK_DEADLOCK FALSE.                                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxRequest, RwTxResponse,
    RoTxRequest, RoTxResponse,
    TxStatusReceived,
    CommittedStatus, InvalidStatus,
    HistoryLimit

ASSUME HistoryLimit \in Nat

ASSUME Cardinality({RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse,
                    TxStatusReceived, CommittedStatus, InvalidStatus}) = 7

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* sequence of ledger branches (only one branch here)
    commitSeqNum     \* highest committed sequence number

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
(* Helpers *)

Range(s) == {s[i] : i \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Ledger == ledgerBranches[Len(ledgerBranches)]

NoDuplicates(s) == \A i, j \in DOMAIN s : s[i] = s[j] => i = j

IsRwResp(i) == history[i].type = RwTxResponse
IsRoResp(i) == history[i].type = RoTxResponse
IsRoReq(i)  == history[i].type = RoTxRequest
IsRwReq(i)  == history[i].type = RwTxRequest
IsStatus(i) == history[i].type = TxStatusReceived
IsReq(i)    == history[i].type \in {RwTxRequest, RoTxRequest}

CommittedTxIdIdx(tid) ==
    {k \in DOMAIN history : IsStatus(k) /\ history[k].tx_id = tid
                            /\ history[k].status = CommittedStatus}

InvalidTxIds ==
    {history[k].tx_id : k \in {k \in DOMAIN history :
        IsStatus(k) /\ history[k].status = InvalidStatus}}

CommittedTxIds ==
    {history[k].tx_id : k \in {k \in DOMAIN history :
        IsStatus(k) /\ history[k].status = CommittedStatus}}

RwRespIdx == {i \in DOMAIN history : IsRwResp(i)}
RoRespIdx == {i \in DOMAIN history : IsRoResp(i)}

CommittedRwRespIdx == {i \in RwRespIdx : history[i].tx_id \in CommittedTxIds}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
(* Single-node read-write actions *)

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRwReq(i)
        /\ \A k \in DOMAIN Ledger : Ledger[k].tx /= history[i].tx
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![1] = Append(@, [view |-> 1, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

RwTxResponseAction ==
    /\ \E j \in DOMAIN Ledger :
        /\ \A k \in DOMAIN history :
              ~(IsRwResp(k) /\ history[k].tx = Ledger[j].tx)
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> Ledger[j].tx,
               observed |-> [k \in 1..j |-> Ledger[k].tx],
               tx_id    |-> <<Ledger[j].view, j>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

CommitAction ==
    /\ commitSeqNum < Len(Ledger)
    /\ commitSeqNum' \in (commitSeqNum + 1)..Len(Ledger)
    /\ UNCHANGED <<history, ledgerBranches>>

StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRwResp(i)
        /\ history[i].tx_id[2] <= commitSeqNum
        /\ ~\E k \in DOMAIN history :
               IsStatus(k) /\ history[k].tx_id = history[i].tx_id
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx_id  |-> history[i].tx_id,
               status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
(* Read-only actions *)

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRoReq(i)
        /\ ~\E k \in DOMAIN history : IsRoResp(k) /\ history[k].tx = history[i].tx
        /\ history' = Append(history,
              [type     |-> RoTxResponse,
               tx       |-> history[i].tx,
               observed |-> [k \in DOMAIN Ledger |-> Ledger[k].tx],
               tx_id    |-> <<1, Len(Ledger)>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
(* Bounded (model-checking) actions *)

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCSingleNodeNext ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ CommitAction
    \/ MCStatusCommittedResponseAction

MCRoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxRequestAction

MCRoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxResponseAction

MCSingleNodeReadsNext ==
    \/ MCSingleNodeNext
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

Next == MCSingleNodeReadsNext

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : Nat]
                   \cup [type : {RwTxResponse, RoTxResponse}, tx : Nat,
                         observed : Seq(Nat), tx_id : Nat \X Nat]
                   \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                         status : {CommittedStatus, InvalidStatus}])
    /\ Len(ledgerBranches) = 1
    /\ commitSeqNum \in 0..Len(Ledger)

\* Each request carries a unique transaction
UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        (IsReq(i) /\ IsReq(j) /\ history[i].tx = history[j].tx) => i = j

\* Each committed transaction identifier maps to a unique Rw transaction
UniqueTxIdsInv ==
    \A i, j \in CommittedRwRespIdx :
        history[i].tx_id = history[j].tx_id => history[i].tx = history[j].tx

\* Each committed sequence number maps to a unique transaction identifier
UniqueSeqNumsInv ==
    \A i, j \in CommittedRwRespIdx :
        history[i].tx_id[2] = history[j].tx_id[2] =>
            history[i].tx_id = history[j].tx_id

\* Committed Rw transactions are serializable
CommittedRwSerializableInv ==
    \A i, j \in CommittedRwRespIdx :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

\* Committed transactions observe only requests sent before their response
CommittedRwOnlyObserveSentRequestsInv ==
    \A i \in CommittedRwRespIdx :
        \A t \in Range(history[i].observed) :
            \E j \in 1..i : IsRwReq(j) /\ history[j].tx = t

\* Responses only observe previously sent Rw requests
AllObserveSentRequestsInv ==
    \A i \in RwRespIdx \cup RoRespIdx :
        \A t \in Range(history[i].observed) :
            \E j \in 1..i : IsRwReq(j) /\ history[j].tx = t

\* Invalid transactions are not observed by committed transactions
InvalidNotObservedByCommittedInv ==
    \A i \in RwRespIdx :
        history[i].tx_id \in InvalidTxIds =>
            \A j \in CommittedRwRespIdx :
                history[i].tx \notin Range(history[j].observed)

\* Each transaction is observed at most once
AtMostOnceObservedInv ==
    \A i \in RwRespIdx \cup RoRespIdx : NoDuplicates(history[i].observed)

\* All committed Rw transactions are observed by later committed Rw transactions
AllCommittedObservedInv ==
    \A i, j \in CommittedRwRespIdx :
        history[i].tx_id[2] <= history[j].tx_id[2] =>
            history[i].tx \in Range(history[j].observed)

\* Every committed Rw transaction observes itself
CommittedRwObservesSelfInv ==
    \A i \in CommittedRwRespIdx :
        /\ Len(history[i].observed) = history[i].tx_id[2]
        /\ history[i].observed[history[i].tx_id[2]] = history[i].tx

\* Ro transactions requested after a commit notification observe that transaction
AllCommittedObservedRoInv ==
    \A i \in CommittedRwRespIdx :
        \A s \in CommittedTxIdIdx(history[i].tx_id) :
            \A r \in DOMAIN history :
                (IsRoReq(r) /\ s < r) =>
                    \A p \in RoRespIdx :
                        history[p].tx = history[r].tx =>
                            history[i].tx \in Range(history[p].observed)

\* Ro transactions observe a prefix consistent with committed Rw transactions
RoObservesConsistentPrefixInv ==
    \A p \in RoRespIdx :
        \A i \in CommittedRwRespIdx :
            \/ IsPrefix(history[p].observed, history[i].observed)
            \/ IsPrefix(history[i].observed, history[p].observed)

=============================================================================