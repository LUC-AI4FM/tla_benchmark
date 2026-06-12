------------------------------ MODULE TraceMultiNodeReads ------------------------------

EXTENDS MultiNodeReads, Json, IOUtils, Sequences, SequencesExt

VARIABLES l

ASSUME TLCGet("config").mode = "bfs" /\ TLCGet("config").worker = 1 /\ TLCSet(0, 0)

MNR == INSTANCE MultiNodeReads

MNRSpec == MNR!Spec

Stats == <<"VARIABLE l (TLCGet(0))", TLCGet(0)>>

JsonFile == IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "trace.ndjson"

JsonLog == JsonFile

TraceInit ==
  /\ MNR!Init
  /\ l = 1

logline == JsonLog[l]

ToTxType ==
  [ s \in {"RwTxRequest", "RwTxResponse", "TxStatusReceived", "RoTxRequest", "RoTxResponse"} |->
      IF s = "RwTxRequest" THEN RwTxRequest
      ELSE IF s = "RwTxResponse" THEN RwTxResponse
      ELSE IF s = "TxStatusReceived" THEN TxStatusReceived
      ELSE IF s = "RoTxRequest" THEN RoTxRequest
      ELSE RoTxResponse ]

ToStatus ==
  [ s \in {"CommittedStatus", "InvalidStatus"} |->
      IF s = "CommittedStatus" THEN CommittedStatus ELSE InvalidStatus ]

IsEvent(actionName, action) ==
  /\ l \in 1..Len(JsonLog)
  /\ logline.action = actionName
  /\ action
  /\ Len(history') > 0
  /\ Last(history').type = ToTxType[logline.type]
  /\ Last(history').tx = logline.tx
  /\ Last(history').tx_id = logline.tx_id
  /\ Last(history').status = ToStatus[logline.status]
  /\ l' = l + 1
  /\ TLCSet(0, l')

IsRwTxRequestAction ==
  IsEvent("RwTxRequestAction", RwTxRequestAction)

IsRwTxExecuteAction ==
  IsEvent("RwTxExecuteAction", RwTxExecuteAction)

IsRwTxResponseAction ==
  IsEvent("RwTxResponseAction", RwTxResponseAction)

IsStatusCommittedResponseAction ==
  IsEvent("StatusCommittedResponseAction", StatusCommittedResponseAction)

IsRoTxRequestAction ==
  IsEvent("RoTxRequestAction", RoTxRequestAction)

IsRoTxResponseAction ==
  IsEvent("RoTxResponseAction", RoTxResponseAction)

IsStatusInvalidResponseAction ==
  IsEvent("StatusInvalidResponseAction", StatusInvalidResponseAction)

PreEvent ==
  /\ l \in 1..Len(JsonLog)
  /\ logline.action = "exit"
  /\ l' = l + 1
  /\ UNCHANGED history
  /\ ledgerBranches' = ledgerBranches
  /\ TLCSet(0, l')

BackfillLedgerBranch(view) ==
  /\ view \in DOMAIN ledgerBranches
  /\ Len(ledgerBranches[view]) < logline.tx_id[2] - 1
  /\ ledgerBranches' = [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
  /\ UNCHANGED history
  /\ l' = l

BackfillLedgerBranchForWrite ==
  LET view == logline.tx_id[1]
      seqno == logline.tx_id[2]
  IN
    /\ l \in 1..Len(JsonLog)
    /\ Len(ledgerBranches[logline.tx_id[1]]) < seqno - 1
    /\ BackfillLedgerBranch(view)

BackfillLedgerBranchForRead ==
  LET view == logline.tx_id[1]
      seqno == logline.tx_id[2]
  IN
    /\ l \in 1..Len(JsonLog)
    /\ Len(ledgerBranches[view]) < seqno - 1
    /\ BackfillLedgerBranch(view)

BackfillLedgerBranches ==
  \/ BackfillLedgerBranchForWrite
  \/ BackfillLedgerBranchForRead

TraceNext ==
  /\ \/ IsRwTxRequestAction
     \/ IsRwTxExecuteAction
     \/ IsRwTxResponseAction
     \/ IsStatusCommittedResponseAction
     \/ IsRoTxRequestAction
     \/ IsRoTxResponseAction
     \/ IsStatusInvalidResponseAction
     \/ PreEvent
     \/ BackfillLedgerBranches
  /\ l' \in {l', TLCGet(0)}

TraceSpec ==
  TraceInit /\ [][TraceNext]_<<l, vars>>

Termination ==
  /\ l > Len(JsonLog)
  /\ TLCSet(0, l) = TRUE

TraceMatched ==
  [](l <= Len(JsonLog) => [](TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog)))

TraceMatchedNonTrivially ==
  TLCGet("queue") \in Nat \ {0} \/ l > Len(JsonLog)

ClientTxnsOnlyAlias ==
  [l |-> l,
   history |-> history,
   ledgerBranches |-> [ b \in DOMAIN ledgerBranches |-> [ e \in { i \in DOMAIN ledgerBranches[b] : "tx" \in DOMAIN ledgerBranches[b][i] } |-> ledgerBranches[b][e] ] ]]

Init == TraceInit

Next == TraceNext

Spec == TraceSpec

=============================================================================