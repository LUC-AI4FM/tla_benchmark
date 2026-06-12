---- MODULE TraceMultiNodeReads ----
EXTENDS MultiNodeReads, Json, IOUtils, Sequences, SequencesExt

VARIABLE l

ASSUME TLCGet("config").mode = "bfs" /\ TLCGet("config").worker = 1 /\ TLCSet(0, 0)

Stats ==
    [ l |-> l,
      history |-> history,
      ledgerBranches |->
        [ b \in DOMAIN ledgerBranches |->
          [ e \in { i \in DOMAIN ledgerBranches[b] :
                    "tx" \in DOMAIN ledgerBranches[b][i] } |->
            ledgerBranches[b][e] ] ] ]

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "trace.ndjson"

JsonLog ==
    JsonDeserialize(JsonFile)

TraceInit ==
    /\ Init
    /\ l = 1

logline ==
    JsonLog[l]

ToTxType ==
    [ t \in {"RwTxRequest", "RwTxResponse", "TxStatusReceived",
             "RoTxRequest", "RoTxResponse"} |-> t ]

ToStatus ==
    [ s \in {"CommittedStatus", "InvalidStatus"} |-> s ]

IsEvent(e) ==
    /\ l \in 1..Len(JsonLog)
    /\ logline.action = e

IsRwTxRequestAction ==
    /\ IsEvent("RwTxRequestAction")
    /\ RwTxRequestAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx = logline.tx

IsRwTxExecuteAction ==
    /\ IsEvent("RwTxExecuteAction")
    /\ RwTxExecuteAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx = logline.tx

IsRwTxResponseAction ==
    /\ IsEvent("RwTxResponseAction")
    /\ RwTxResponseAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx = logline.tx
    /\ Last(history').tx_id = logline.tx_id
    /\ Last(history').status = ToStatus[logline.status]

IsStatusCommittedResponseAction ==
    /\ IsEvent("StatusCommittedResponseAction")
    /\ StatusCommittedResponseAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx_id = logline.tx_id
    /\ Last(history').status = ToStatus[logline.status]

IsRoTxRequestAction ==
    /\ IsEvent("RoTxRequestAction")
    /\ RoTxRequestAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx = logline.tx

IsRoTxResponseAction ==
    /\ IsEvent("RoTxResponseAction")
    /\ RoTxResponseAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx = logline.tx
    /\ Last(history').tx_id = logline.tx_id
    /\ Last(history').status = ToStatus[logline.status]

IsStatusInvalidResponseAction ==
    /\ IsEvent("StatusInvalidResponseAction")
    /\ StatusInvalidResponseAction
    /\ Last(history').type = ToTxType[logline.type]
    /\ Last(history').tx_id = logline.tx_id
    /\ Last(history').status = ToStatus[logline.status]

PreEvent ==
    /\ \/ IsRwTxRequestAction
       \/ IsRwTxExecuteAction
       \/ IsRwTxResponseAction
       \/ IsStatusCommittedResponseAction
       \/ IsRoTxRequestAction
       \/ IsRoTxResponseAction
       \/ IsStatusInvalidResponseAction
    /\ l' = l + 1
    /\ TLCSet(0, {l', TLCGet(0)})

BackfillLedgerBranch(view) ==
    /\ view \in DOMAIN ledgerBranches
    /\ ledgerBranches' =
        [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
    /\ UNCHANGED history

BackfillLedgerBranchForWrite ==
    LET view == logline.tx_id[1]
        seqno == logline.tx_id[2]
    IN
        /\ \/ IsEvent("RwTxResponseAction")
           \/ IsEvent("StatusCommittedResponseAction")
        /\ logline.tx_id[1] \in DOMAIN ledgerBranches
        /\ Len(ledgerBranches[logline.tx_id[1]]) < logline.tx_id[2] - 1
        /\ Len(ledgerBranches[view]) >= 0
        /\ seqno >= 1
        /\ BackfillLedgerBranch(view)

BackfillLedgerBranchForRead ==
    LET view == logline.tx_id[1]
        seqno == logline.tx_id[2]
    IN
        /\ \/ IsEvent("RoTxResponseAction")
           \/ IsEvent("StatusInvalidResponseAction")
        /\ logline.tx_id[1] \in DOMAIN ledgerBranches
        /\ Len(ledgerBranches[logline.tx_id[1]]) < logline.tx_id[2]
        /\ Len(ledgerBranches[view]) < seqno
        /\ seqno >= 1
        /\ BackfillLedgerBranch(view)

BackfillLedgerBranches ==
    /\ \/ BackfillLedgerBranchForWrite
       \/ BackfillLedgerBranchForRead
    /\ l' = l

TraceNext ==
    \/ /\ l <= Len(JsonLog)
       /\ PreEvent
    \/ /\ l <= Len(JsonLog)
       /\ BackfillLedgerBranches
    \/ Termination

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<l, vars>>

Termination ==
    /\ l > Len(JsonLog)
    /\ TLCSet("exit", <<"VARIABLE l (TLCGet(0))", TLCGet(0)>>)

TraceMatched ==
    [](l <= Len(JsonLog) => [](TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog)))

TraceMatchedNonTrivially ==
    TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog)

MNR == INSTANCE MultiNodeReads

MNRSpec ==
    MNR!Spec

ClientTxnsOnlyAlias ==
    MNR!ClientTxnsOnly

====