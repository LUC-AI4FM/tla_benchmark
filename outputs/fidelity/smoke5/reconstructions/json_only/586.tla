---- MODULE TraceMultiNodeReads ----
EXTENDS MultiNodeReads, Json, IOUtils, Sequences, SequencesExt

VARIABLE l

ASSUME TLCGet("config").mode = "bfs" /\ TLCGet("config").worker = 1 /\ TLCSet(0, 0)

MNR == INSTANCE MultiNodeReads

MNRSpec == MNR!Spec

ClientTxnsOnlyAlias == MNR!ClientTxnsOnly

JsonFile == IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "trace.ndjson"

JsonLog == JsonFile

Stats ==
  << <<"VARIABLE l (TLCGet(0))", TLCGet(0)>>,
     [ l |-> l,
       history |-> history,
       ledgerBranches |->
         [ b \in DOMAIN ledgerBranches |->
           [ e \in { i \in DOMAIN ledgerBranches[b] : "tx" \in DOMAIN ledgerBranches[b][i] } |->
             ledgerBranches[b][e] ] ] ] >>

TraceInit ==
  /\ MNR!Init
  /\ l = 1

logline == JsonLog[l]

ToTxType ==
  << "RwTxRequest",
     "RwTxResponse",
     "TxStatusReceived",
     "RoTxRequest",
     "RoTxResponse" >>

ToStatus ==
  << "CommittedStatus",
     "InvalidStatus" >>

IsEvent(action) ==
  /\ l >= 1
  /\ l <= Len(JsonLog)
  /\ l \in 1..Len(JsonLog)
  /\ logline.action = action

IsRwTxRequestAction ==
  /\ IsEvent("RwTxRequestAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsRwTxExecuteAction ==
  /\ IsEvent("RwTxExecuteAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsRwTxResponseAction ==
  /\ IsEvent("RwTxResponseAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsStatusCommittedResponseAction ==
  /\ IsEvent("StatusCommittedResponseAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ Last(history').status = ToStatus[logline.status]
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsRoTxRequestAction ==
  /\ IsEvent("RoTxRequestAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsRoTxResponseAction ==
  /\ IsEvent("RoTxResponseAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

IsStatusInvalidResponseAction ==
  /\ IsEvent("StatusInvalidResponseAction")
  /\ history' = Append(history, logline)
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ Last(history').status = ToStatus[logline.status]
  /\ l' = l + 1
  /\ ledgerBranches' = ledgerBranches

PreEvent ==
  /\ l <= Len(JsonLog)
  /\ l' = l
  /\ l' \in {l', TLCGet(0)}
  /\ UNCHANGED history
  /\ ledgerBranches' = ledgerBranches

BackfillLedgerBranch ==
  LET view == logline.tx_id[1]
      seqno == logline.tx_id[2]
  IN
    /\ view \in DOMAIN ledgerBranches
    /\ Len(ledgerBranches[view]) < seqno - 1
    /\ ledgerBranches' =
         [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
    /\ l' = l
    /\ UNCHANGED history

BackfillLedgerBranchForWrite ==
  /\ IsEvent("RwTxExecuteAction")
  /\ BackfillLedgerBranch

BackfillLedgerBranchForRead ==
  /\ IsEvent("RoTxResponseAction")
  /\ BackfillLedgerBranch

BackfillLedgerBranches ==
  \/ BackfillLedgerBranchForWrite
  \/ BackfillLedgerBranchForRead

Termination ==
  /\ l > Len(JsonLog)
  /\ TLCSet("exit", TRUE)

TraceNext ==
  \/ IsRwTxRequestAction
  \/ IsRwTxExecuteAction
  \/ IsRwTxResponseAction
  \/ IsStatusCommittedResponseAction
  \/ IsRoTxRequestAction
  \/ IsRoTxResponseAction
  \/ IsStatusInvalidResponseAction
  \/ BackfillLedgerBranches
  \/ PreEvent
  \/ /\ Termination
     /\ l' = l
     /\ UNCHANGED history
     /\ ledgerBranches' = ledgerBranches

TraceSpec ==
  /\ TraceInit
  /\ [][TraceNext]_<<l, vars>>

TraceMatched ==
  [](l <= Len(JsonLog) => [](TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog)))

TraceMatchedNonTrivially ==
  [](TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog))

====