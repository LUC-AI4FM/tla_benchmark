------------------------------- MODULE MCSpecMultiNodeReadsAlt -------------------------------

EXTENDS MCBaseSpec

CONSTANTS vars

VARIABLES ledger, history

(*--algorithm MultiNodeReadsAlt
variables 
    ledger = [branch \in BRANCHES |-> <<>>],
    history = <<>>,
    committedTransactions = {"tx1", "tx2"};

begin
    with
        ledger' = [ledger EXCEPT ![BRANCH_1] = <<TX_RECORD["tx1"]>>, ![BRANCH_2] = <<TX_RECORD["tx2"]>>],
        history' = <<HISTORY_RECORD["tx1"], HISTORY_RECORD["tx2"]>>
    do
        /\ InitState(ledger', history')
        /\ MCNextMultiNodeReadsAction
end with;
end algorithm;*)

InitState(ledger, history) == 
    /\ ledger[BRANCH_1] = <<TX_RECORD["tx1"]>>
    /\ ledger[BRANCH_2] = <<TX_RECORD["tx2"]>>
    /\ history = <<HISTORY_RECORD["tx1"], HISTORY_RECORD["tx2"]>>

MCSpecMultiNodeReadsAlt == InitState(ledger, history) /\ [][MCNextMultiNodeReadsAction]_<<vars>>

=============================================================================