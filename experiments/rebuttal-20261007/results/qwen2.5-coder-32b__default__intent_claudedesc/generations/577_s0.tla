------------------------------- MODULE DistributedLedger -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,          \* Set of nodes in the system
    Clients         \* Set of clients submitting transactions

VARIABLES 
    ledger,         \* A mapping from view numbers to sequences of committed transactions
    pendingTxs,     \* A set of pending transactions
    txStatus,       \* A mapping from transaction IDs to their status (committed, pending)
    clientRequests, \* A mapping from clients to a sequence of their submitted transactions
    clientResponses,\* A mapping from clients to a sequence of responses they received
    viewNumber      \* The current view number

Init == 
    /\ ledger = [v \in Nat |-> <<>>]
    /\ pendingTxs = {}
    /\ txStatus = [t \in (DOMAIN clientRequests) \cup (DOMAIN clientResponses) |-> "pending"]
    /\ clientRequests = [c \in Clients |-> <>]
    /\ clientResponses = [c \in Clients |-> <>]
    /\ viewNumber = 0

InitMidExecution == 
    /\ ledger = [v \in {0, 1} |-> <<>>] 
       \* Example: Two branches with no transactions yet
    /\ ledger[0] = <<1, 2>> 
       \* Branch 0 has transactions 1 and 2 committed
    /\ ledger[1] = <<3>> 
       \* Branch 1 has transaction 3 committed
    /\ pendingTxs = {4, 5} 
       \* Transactions 4 and 5 are pending
    /\ txStatus = [t \in {1, 2, 3, 4, 5} |-> IF t \in {1, 2, 3} THEN "committed" ELSE "pending"]
    /\ clientRequests = [c \in Clients |-> <>]
    /\ clientResponses = [c \in Clients |-> <>]
    /\ viewNumber = 1

Next == 
    \/ \E c \in Clients, tx \notin DOMAIN txStatus : SubmitTx(c, tx)
    \/ \E v \in Nat, seqNum \in Nat, tx \in pendingTxs : CommitTx(v, seqNum, tx)

SubmitTx(c, tx) ==
    /\ clientRequests' = [clientRequests EXCEPT ![c] = Append(clientRequests[c], tx)]
    /\ pendingTxs' = pendingTxs \cup {tx}
    /\ txStatus' = [txStatus EXCEPT ![tx] = "pending"]

CommitTx(v, seqNum, tx) ==
    /\ pendingTxs' = pendingTxs \ {tx}
    /\ ledger' = [ledger EXCEPT ![v] = Append(ledger[v], <<tx>>)]
    /\ txStatus' = [txStatus EXCEPT ![tx] = "committed"]
    /\ viewNumber' = v

Spec == 
    \/ Init /\ [][Next]_<<pendingTxs, txStatus, clientRequests, clientResponses, viewNumber>>
    \/ InitMidExecution /\ [][Next]_<<pendingTxs, txStatus, clientRequests, clientResponses, viewNumber>>

ReadConsistency ==
    \A c1, c2 \in Clients, i, j \in Nat :
        (i < Len(clientResponses[c1]) /\ j < Len(clientResponses[c2])
         => LET resp1 == clientResponses[c1][i]
                resp2 == clientResponses[c2][j]
            IN  \A txID1 \in resp1.transactionsSeen,
                    txID2 \in resp2.transactionsSeen :
                    (txStatus[txID1] = "committed" /\ txStatus[txID2] = "committed"
                     => txID1 < txID2 <=> ledger[viewNumber][IndexOf(ledger[viewNumber], txID1)] < IndexOf(ledger[viewNumber], txID2)))

BranchConsistency ==
    \A v1, v2 \in Nat :
        (v1 /= v2
         => \E seqNum1 \in DOMAIN ledger[v1], seqNum2 \in DOMAIN ledger[v2] :
                ledger[v1][seqNum1] = ledger[v2][seqNum2]
                => \A txID \in {ledger[v1][seqNum1], ledger[v2][seqNum2]} :
                    txStatus[txID] = "committed")

Linearizability ==
    \A c \in Clients, i \in Nat :
        (i < Len(clientRequests[c])
         => LET req == clientRequests[c][i]
                resp == clientResponses[c][i]
            IN  \E seqNum \in DOMAIN ledger[viewNumber] :
                    ledger[viewNumber][seqNum] = req
                    /\ \A j \in Nat : (j < i => txStatus[clientRequests[c][j]] = "committed")
                    /\ \A k \in Nat : (k > i => txStatus[clientResponses[c][k].transactionID] = "pending"))

SpecWithProperties ==
    Spec /\ []ReadConsistency
         /\ []BranchConsistency
         /\ []Linearizability

Fairness == 
    WF_next(Next)

CompleteSpec == SpecWithProperties /\ Fairness

=============================================================================