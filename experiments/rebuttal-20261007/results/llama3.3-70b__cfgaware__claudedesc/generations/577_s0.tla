--------------------------- MODULE MCMultiNodeReadsAlt ---------------------------
EXTENDS MCMultiNodeReads
VARIABLES msgQueue, history, ledger, view, txStatus, seqNum, txId, readSet

HistoryLimit == 11
ViewLimit == 3

InitAlt ==
  /\ msgQueue = <<>>
  /\ history = <<
    <<REQUEST, 1, "tx1">>,
    <<RESPONSE, 1, "tx1", TRUE>>,
    <<COMMIT, 1, "tx1">>,
    <<REQUEST, 2, "tx2">>,
    <<RESPONSE, 2, "tx2", TRUE>>,
    <<COMMIT, 2, "tx2">>
  >>
  /\ ledger = [view |-> <<>>, txId |-> <<>>]
  /\ view = 3
  /\ txStatus = [tx1 |-> COMMITTED, tx2 |-> COMMITTED]
  /\ seqNum = 3
  /\ txId = {"tx1", "tx2"}
  /\ readSet = {}

MCNextMultiNodeReadsAction == 
  MCNextMultiNodeReadsAction

MCSpecMultiNodeReadsAlt ==
  /\ InitAlt
  /\ [][MCNextMultiNodeReadsAction]_msgQueue
  /\ WF_vars(MCNextMultiNodeReadsAction, msgQueue)
  /\ Deadlock == FALSE

THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []Inv4
THEOREM Spec => []Inv5
THEOREM Spec => []Inv6
THEOREM Spec => []Inv7
THEOREM Spec => []Inv8
THEOREM Spec => []Inv9
THEOREM Spec => []Inv10
THEOREM Spec => []Inv11
THEOREM Spec => []Inv12

===============================================================================