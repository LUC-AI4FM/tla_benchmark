---- MODULE SingleNodeReads ----
EXTENDS Naturals, Sequences, FiniteSets

\* ------------------------------------------------------------------
\* Base SingleNode model, inlined so this module stands alone
\* ------------------------------------------------------------------

CONSTANTS
    RwTxRequest, RwTxResponse,
    RoTxRequest, RoTxResponse,
    TxStatusReceived,
    CommittedStatus, InvalidStatus

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

FirstBranch == 1

LatestBranch == ledgerBranches[Len(ledgerBranches)]

\* Request ids are unique and grow monotonically
NumRequests ==
    Cardinality({i \in DOMAIN history :
                    history[i].type \in {RwTxRequest, RoTxRequest}})

NextRequestId == NumRequests + 1

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

\* Submit a new read-write transaction
RwTxnRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction by appending it to the latest branch
RwTxnExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A seqnum \in DOMAIN LatestBranch : LatestBranch[seqnum].tx # history[i].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(LatestBranch, [view |-> Len(ledgerBranches), tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to a read-write transaction that has been executed
RwTxnResponseAction ==
    /\ \E view \in FirstBranch..Len(ledgerBranches) :
        \E seqnum \in DOMAIN ledgerBranches[view] :
            /\ \A k \in DOMAIN history :
                history[k].type = RwTxResponse => history[k].tx # ledgerBranches[view][seqnum].tx
            /\ history' = Append(history, [
                    type |-> RwTxResponse,
                    tx |-> ledgerBranches[view][seqnum].tx,
                    observed |-> [s \in 1..seqnum |-> ledgerBranches[view][s].tx],
                    tx_id |-> <<ledgerBranches[view][seqnum].view, seqnum>>])
    /\ UNCHANGED ledgerBranches

\* Report the status of a transaction that received a response
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET view == history[i].tx_id[1]
               seqnum == history[i].tx_id[2]
           IN /\ seqnum \in DOMAIN LatestBranch
              /\ LatestBranch[seqnum].view = view
              /\ \A k \in DOMAIN history :
                    history[k].type = TxStatusReceived => history[k].tx_id # history[i].tx_id
              /\ history' = Append(history, [
                    type |-> TxStatusReceived,
                    tx_id |-> history[i].tx_id,
                    status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Simulate a view change: start a new branch from a prefix of the latest one
TruncateLedgerAction ==
    /\ \E i \in 0..Len(LatestBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(LatestBranch, 1, i))
    /\ UNCHANGED history

NextSingleNodeAction ==
    \/ RwTxnRequestAction
    \/ RwTxnExecuteAction
    \/ RwTxnResponseAction
    \/ StatusCommittedResponseAction
    \/ TruncateLedgerAction

\* ------------------------------------------------------------------
\* Read-only extension
\* ------------------------------------------------------------------

\* Submit a new read-only transaction
RoTxnRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-only transaction and respond in a single atomic step.
\* Read-only transactions are always forwarded, so they may observe any branch.
RoTxnResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A k \in DOMAIN history :
            history[k].type = RoTxResponse => history[k].tx # history[i].tx
        /\ \E view \in FirstBranch..Len(ledgerBranches) :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(history, [
                    type |-> RoTxResponse,
                    tx |-> history[i].tx,
                    observed |-> [seqnum \in DOMAIN ledgerBranches[view] |->
                                    ledgerBranches[view][seqnum].tx],
                    tx_id |-> <<ledgerBranches[view][Len(ledgerBranches[view])].view,
                                Len(ledgerBranches[view])>>])
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxnRequestAction
    \/ RoTxnResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

\* ------------------------------------------------------------------
\* Invariants
\* ------------------------------------------------------------------

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RwTxResponse, RoTxRequest,
                               RoTxResponse, TxStatusReceived}] \cup
                       {h : h \in {history[i] : i \in DOMAIN history}})
    /\ ledgerBranches \in Seq(Seq([view : Nat, tx : Nat]))
    /\ Len(ledgerBranches) >= 1

\* Every read-only response answers an earlier read-only request
RoResponseHasRequestInv ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = RoTxRequest
                /\ history[j].tx = history[i].tx

\* Each read-only request gets at most one response
UniqueRoResponseInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RoTxResponse
         /\ history[j].type = RoTxResponse
         /\ history[i].tx = history[j].tx) => i = j

====