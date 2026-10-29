---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    \* Finite set of request identifiers available to clients
    Txs

VARIABLES
    \* Sequence of externally visible events (requests, responses, statuses)
    history,
    \* Indexed collection of append-only ledgers. ledgerBranches[v] is the
    \* leader's log in view v.
    ledgerBranches

vars == <<history, ledgerBranches>>

-----------------------------------------------------------------------------
\* Event types and statuses

RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"
TxStatuses       == {CommittedStatus, InvalidStatus}

\* With a single node there is only ever one view
FirstBranch == 1
Views == Nat \ {0}
SeqNums == Nat \ {0}
TxIDs == Views \X SeqNums

-----------------------------------------------------------------------------
\* Helpers

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

HasTx(e) == "tx" \in DOMAIN e

\* The sequence of transaction identifiers recorded in a ledger prefix
TxsOf(s) ==
    LET f == SelectSeq(s, HasTx)
    IN [k \in DOMAIN f |-> f[k].tx]

HighestView == Len(ledgerBranches)

RequestedTxs ==
    { history[i].tx :
        i \in { j \in DOMAIN history : history[j].type = RwTxRequest } }

RespondedTxs ==
    { history[i].tx :
        i \in { j \in DOMAIN history : history[j].type = RwTxResponse } }

ExecutedTxs ==
    { ledgerBranches[v][i].tx :
        <<v, i>> \in { <<w, k>> \in (DOMAIN ledgerBranches) \X SeqNums :
                         /\ k \in DOMAIN ledgerBranches[w]
                         /\ HasTx(ledgerBranches[w][k]) } }

-----------------------------------------------------------------------------
\* Type invariants

LedgerEntryOK(e) ==
    /\ "view" \in DOMAIN e
    /\ e.view \in Views
    /\ HasTx(e) => e.tx \in Txs

LedgerTypeOK(ledger) ==
    \A i \in DOMAIN ledger : LedgerEntryOK(ledger[i])

EventOK(ev) ==
    \/ /\ ev.type = RwTxRequest
       /\ ev.tx \in Txs
    \/ /\ ev.type = RwTxResponse
       /\ ev.tx \in Txs
       /\ ev.tx_id \in TxIDs
       /\ \A k \in DOMAIN ev.observed : ev.observed[k] \in Txs
    \/ /\ ev.type = TxStatusReceived
       /\ ev.tx_id \in TxIDs
       /\ ev.status \in TxStatuses

TypeOK ==
    /\ \A i \in DOMAIN history : EventOK(history[i])
    /\ DOMAIN ledgerBranches = 1..Len(ledgerBranches)
    /\ \A v \in DOMAIN ledgerBranches : LedgerTypeOK(ledgerBranches[v])

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = <<<<>>>>

-----------------------------------------------------------------------------
\* Actions

\* Submit a new read-write transaction with a fresh unique identifier
RwTxRequestAction ==
    /\ \E tx \in Txs \ RequestedTxs :
         history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
    /\ UNCHANGED ledgerBranches

\* Execute a pending request by appending it to some ledger branch
RwTxExecuteAction ==
    /\ \E view \in DOMAIN ledgerBranches :
         \E tx \in RequestedTxs \ ExecutedTxs :
            ledgerBranches' =
                [ledgerBranches EXCEPT ![view] =
                    Append(@, [view |-> view, tx |-> tx])]
    /\ UNCHANGED history

\* Respond to an executed but not yet answered request
RwTxResponseAction ==
    /\ \E view \in DOMAIN ledgerBranches :
         \E i \in DOMAIN ledgerBranches[view] :
            LET e == ledgerBranches[view][i]
            IN /\ HasTx(e)
               /\ e.tx \in RequestedTxs
               /\ e.tx \notin RespondedTxs
               /\ history' = Append(history,
                     [type     |-> RwTxResponse,
                      tx       |-> e.tx,
                      observed |-> TxsOf(SubSeq(ledgerBranches[view], 1, i)),
                      tx_id    |-> <<e.view, i>>])
    /\ UNCHANGED ledgerBranches

\* Report a transaction as committed
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RwTxResponse
         /\ LET view   == history[i].tx_id[1]
                seqnum == history[i].tx_id[2]
                ledger == ledgerBranches[HighestView]
            IN /\ seqnum \in DOMAIN ledger
               /\ ledger[seqnum].view = view
               /\ ~ \E j \in DOMAIN history :
                      /\ history[j].type = TxStatusReceived
                      /\ history[j].tx_id = history[i].tx_id
                      /\ history[j].status = InvalidStatus
               /\ history' = Append(history,
                     [type   |-> TxStatusReceived,
                      tx_id  |-> history[i].tx_id,
                      status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Append ledger entries not associated with client transactions
AppendOtherTxnAction ==
    /\ \E view \in DOMAIN ledgerBranches :
         ledgerBranches' =
             [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

SpecSingleNode == Init /\ [][Next]_vars

Spec == SpecSingleNode

-----------------------------------------------------------------------------
\* Temporal properties

\* Every ledger branch is append-only
LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches :
          /\ view \in DOMAIN ledgerBranches'
          /\ IsPrefix(ledgerBranches[view], ledgerBranches'[view])
      ]_ledgerBranches

THEOREM SpecSingleNode => []TypeOK
THEOREM SpecSingleNode => LedgersMonoProp

=============================================================================