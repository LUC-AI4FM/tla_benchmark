---------------------------- MODULE MCSingleNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    HistoryLimit,
    ViewLimit

ASSUME HistoryLimit \in Nat
ASSUME ViewLimit \in Nat \ {0}

VARIABLES
    history,
    ledger,
    view

vars == <<history, ledger, view>>

RwTxRequest  == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest  == "RoTxRequest"
RoTxResponse == "RoTxResponse"

IsPrefix(s, t) ==
    Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

LedgerTxs == [j \in 1..Len(ledger) |-> ledger[j].tx]

RequestIndices ==
    {i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}}

NextRequestId == Cardinality(RequestIndices) + 1

HasResponse(t) ==
    \E i \in DOMAIN history :
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ history[i].tx = t

InLedger(t) == \E j \in DOMAIN ledger : ledger[j].tx = t

-----------------------------------------------------------------------------
\* Single-node base system

Init ==
    /\ history = <<>>
    /\ ledger = <<>>
    /\ view = 1

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledger, view>>

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~InLedger(history[i].tx)
        /\ ledger' = Append(ledger, [view |-> view, tx |-> history[i].tx])
    /\ UNCHANGED <<history, view>>

RwTxResponseAction ==
    /\ \E j \in DOMAIN ledger :
        /\ ~HasResponse(ledger[j].tx)
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> ledger[j].tx,
               observed |-> [k \in 1..j |-> ledger[k].tx],
               tx_id    |-> <<ledger[j].view, j>>])
    /\ UNCHANGED <<ledger, view>>

NewViewAction ==
    /\ view < ViewLimit
    /\ view' = view + 1
    /\ UNCHANGED <<history, ledger>>

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledger, view>>

RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~HasResponse(history[i].tx)
        /\ history' = Append(history,
              [type     |-> RoTxResponse,
               tx       |-> history[i].tx,
               observed |-> LedgerTxs,
               tx_id    |-> <<view, Len(ledger)>>])
    /\ UNCHANGED <<ledger, view>>

-----------------------------------------------------------------------------
\* Bounded model-checking wrappers

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCNextSingleNodeAction ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ NewViewAction

MCRoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxRequestAction

MCRoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxResponseAction

MCNextSingleNodeReadsAction ==
    \/ MCNextSingleNodeAction
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

Next == MCNextSingleNodeReadsAction

MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReadsAction]_vars

Spec == MCSpecSingleNodeReads

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : Nat]
                       \cup [type : {RwTxResponse, RoTxResponse}, tx : Nat,
                             observed : Seq(Nat), tx_id : Nat \X Nat])
    /\ ledger \in Seq([view : Nat, tx : Nat])
    /\ view \in 1..ViewLimit

HistoryBoundInv ==
    Len(history) <= HistoryLimit

ObservedPrefixOfLedgerInv ==
    \A i \in DOMAIN history :
        history[i].type \in {RwTxResponse, RoTxResponse}
            => IsPrefix(history[i].observed, LedgerTxs)

=============================================================================