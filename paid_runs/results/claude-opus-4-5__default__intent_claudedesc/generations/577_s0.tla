---------------------------- MODULE DistributedLedger ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Clients,           \* Set of client identifiers
    MaxView,           \* Maximum view number
    MaxSeq,            \* Maximum sequence number per view
    MaxTransactions    \* Maximum number of transactions to model

VARIABLES
    ledger,            \* Function: [branch -> Seq(Transaction)]
    branches,          \* Set of active branch identifiers (view numbers)
    pendingRequests,   \* Set of pending transaction requests
    responses,         \* Set of transaction responses sent to clients
    txStatus,          \* Function: [TxID -> {"pending", "committed"}]
    clientState,       \* Function: [client -> record of client's view]
    nextSeq,           \* Function: [view -> next sequence number]
    statusNotifications \* Set of status change notifications sent

vars == <<ledger, branches, pendingRequests, responses, txStatus, clientState, nextSeq, statusNotifications>>

\* Type definitions
TxID == [view: 0..MaxView, seq: 0..MaxSeq]

NullTxID == [view |-> -1, seq |-> -1]

Transaction == [
    id: TxID,
    client: Clients,
    observedTxs: SUBSET TxID,
    data: Nat
]

Request == [
    client: Clients,
    data: Nat,
    observing: SUBSET TxID
]

Response == [
    client: Clients,
    txId: TxID,
    observedPrior: SUBSET TxID,
    branch: 0..MaxView
]

StatusNotification == [
    client: Clients,
    txId: TxID,
    status: {"committed"}
]

\* Helper functions

\* Get all transaction IDs on a branch
TxIDsOnBranch(branch) ==
    IF branch \in DOMAIN ledger
    THEN {ledger[branch][i].id : i \in 1..Len(ledger[branch])}
    ELSE {}

\* Get all committed transaction IDs
CommittedTxIDs ==
    {txId \in DOMAIN txStatus : txStatus[txId] = "committed"}

\* Check if txId1 is before or equal to txId2 in ordering
TxIDLeq(txId1, txId2) ==
    \/ txId1.view < txId2.view
    \/ (txId1.view = txId2.view /\ txId1.seq <= txId2.seq)

\* Get all transaction IDs that precede a given txId on a branch
PrecedingTxIDs(branch, txId) ==
    IF branch \in DOMAIN ledger
    THEN {ledger[branch][i].id : i \in {j \in 1..Len(ledger[branch]) : 
            TxIDLeq(ledger[branch][j].id, txId) /\ ledger[branch][j].id # txId}}
    ELSE {}

\* Total number of transactions across all branches
TotalTransactions ==
    LET branchSet == DOMAIN ledger
    IN IF branchSet = {} THEN 0
       ELSE LET lens == {Len(ledger[b]) : b \in branchSet}
            IN IF lens = {} THEN 0
               ELSE LET maxLen == CHOOSE x \in lens : \A y \in lens : x >= y
                    IN maxLen * Cardinality(branchSet)

\* Initial state - empty ledger
Init ==
    /\ ledger = [b \in {0} |-> <<>>]
    /\ branches = {0}
    /\ pendingRequests = {}
    /\ responses = {}
    /\ txStatus = [t \in {} |-> "pending"]
    /\ clientState = [c \in Clients |-> [
            lastObserved |-> {},
            pendingTxs |-> {},
            committedTxs |-> {}
       ]]
    /\ nextSeq = [v \in 0..MaxView |-> 0]
    /\ statusNotifications = {}

\* Alternative initial state - mid-execution with existing transactions
InitMidExecution ==
    LET 
        \* Pre-existing transactions on branch 0
        tx0_0 == [id |-> [view |-> 0, seq |-> 0], client |-> CHOOSE c \in Clients : TRUE, 
                  observedTxs |-> {}, data |-> 1]
        tx0_1 == [id |-> [view |-> 0, seq |-> 1], client |-> CHOOSE c \in Clients : TRUE,
                  observedTxs |-> {[view |-> 0, seq |-> 0]}, data |-> 2]
        \* Pre-existing transaction on branch 1 (fork)
        tx1_0 == [id |-> [view |-> 1, seq |-> 0], client |-> CHOOSE c \in Clients : TRUE,
                  observedTxs |-> {[view |-> 0, seq |-> 0]}, data |-> 3]
        
        initialClient == CHOOSE c \in Clients : TRUE
    IN
    /\ ledger = [b \in {0, 1} |-> 
            IF b = 0 THEN <<tx0_0, tx0_1>>
            ELSE <<tx1_0>>]
    /\ branches = {0, 1}
    /\ pendingRequests = {}
    /\ responses = {
            [client |-> initialClient, txId |-> [view |-> 0, seq |-> 0], 
             observedPrior |-> {}, branch |-> 0],
            [client |-> initialClient, txId |-> [view |-> 0, seq |-> 1],
             observedPrior |-> {[view |-> 0, seq |-> 0]}, branch |-> 0],
            [client |-> initialClient, txId |-> [view |-> 1, seq |-> 0],
             observedPrior |-> {[view |-> 0, seq |-> 0]}, branch |-> 1]
       }
    /\ txStatus = [t \in {[view |-> 0, seq |-> 0], [view |-> 0, seq |-> 1], [view |-> 1, seq |-> 0]} |->
            IF t = [view |-> 1, seq |-> 0] THEN "pending" ELSE "committed"]
    /\ clientState = [c \in Clients |-> [
            lastObserved |-> {[view |-> 0, seq |-> 0], [view |-> 0, seq |-> 1]},
            pendingTxs |-> IF c = initialClient THEN {[view |-> 1, seq |-> 0]} ELSE {},
            committedTxs |-> {[view |-> 0, seq |-> 0], [view |-> 0, seq |-> 1]}
       ]]
    /\ nextSeq = [v \in 0..MaxView |-> IF v = 0 THEN 2 ELSE IF v = 1 THEN 1 ELSE 0]
    /\ statusNotifications = {
            [client |-> initialClient, txId |-> [view |-> 0, seq |-> 0], status |-> "committed"],
            [client |-> initialClient, txId |-> [view |-> 0, seq |-> 1], status |-> "committed"]
       }

\* Actions

\* Client submits a new transaction request
SubmitTransaction(client, data) ==
    LET observing == clientState[client].lastObserved
    IN
    /\ Cardinality(pendingRequests) < MaxTransactions
    /\ pendingRequests' = pendingRequests \cup {[
            client |-> client,
            data |-> data,
            observing |-> observing
       ]}
    /\ UNCHANGED <<ledger, branches, responses, txStatus, clientState, nextSeq, statusNotifications>>

\* System processes a pending request and adds to ledger
ProcessTransaction(req, branch) ==
    LET 
        view == branch
        seq == nextSeq[view]
        txId == [view |-> view, seq |-> seq]
        priorOnBranch == TxIDsOnBranch(branch)
        observedPrior == req.observing \cup priorOnBranch
        newTx == [
            id |-> txId,
            client |-> req.client,
            observedTxs |-> observedPrior,
            data |-> req.data
        ]
        newResponse == [
            client |-> req.client,
            txId |-> txId,
            observedPrior |-> observedPrior,
            branch |-> branch
        ]
    IN
    /\ req \in pendingRequests
    /\ branch \in branches
    /\ seq <= MaxSeq
    /\ view <= MaxView
    /\ pendingRequests' = pendingRequests \ {req}
    /\ ledger' = [ledger EXCEPT ![branch] = Append(@, newTx)]
    /\ responses' = responses \cup {newResponse}
    /\ txStatus' = txId :> "pending" @@ txStatus
    /\ clientState' = [clientState EXCEPT 
            ![req.client].pendingTxs = @ \cup {txId},
            ![req.client].lastObserved = @ \cup {txId}]
    /\ nextSeq' = [nextSeq EXCEPT ![view] = @ + 1]
    /\ UNCHANGED <<branches, statusNotifications>>

\* Transaction becomes committed
CommitTransaction(txId) ==
    /\ txId \in DOMAIN txStatus
    /\ txStatus[txId] = "pending"
    /\ txStatus' = [txStatus EXCEPT ![txId] = "committed"]
    /\ LET affectedClients == {c \in Clients : txId \in clientState[c].pendingTxs}
           newNotifications == {[client |-> c, txId |-> txId, status |-> "committed"] : c \in affectedClients}
       IN
       /\ statusNotifications' = statusNotifications \cup newNotifications
       /\ clientState' = [c \in Clients |-> 
              IF c \in affectedClients
              THEN [clientState[c] EXCEPT 
                      !.pendingTxs = @ \ {txId},
                      !.committedTxs = @ \cup {txId}]
              ELSE clientState[c]]
    /\ UNCHANGED <<ledger, branches, pendingRequests, responses, nextSeq>>

\* Create a new branch (fork) - models view change
CreateBranch(parentBranch, forkPoint) ==
    LET newView == (CHOOSE v \in 0..MaxView : v \notin branches /\ v > parentBranch)
        parentTxs == IF parentBranch \in DOMAIN ledger 
                     THEN SubSeq(ledger[parentBranch], 1, forkPoint)
                     ELSE <<>>
    IN
    /\ \E v \in 0..MaxView : v \notin branches /\ v > parentBranch
    /\ parentBranch \in branches
    /\ forkPoint >= 0
    /\ forkPoint <= Len(ledger[parentBranch])
    /\ branches' = branches \cup {newView}
    /\ ledger' = newView :> parentTxs @@ ledger
    /\ nextSeq' = [nextSeq EXCEPT ![newView] = forkPoint]
    /\ UNCHANGED <<pendingRequests, responses, txStatus, clientState, statusNotifications>>

\* Client observes a transaction (updates their view)
ClientObservesTx(client, txId) ==
    /\ txId \in DOMAIN txStatus
    /\ txStatus[txId] = "committed"
    /\ txId \notin clientState[client].lastObserved
    /\ clientState' = [clientState EXCEPT 
            ![client].lastObserved = @ \cup {txId},
            ![client].committedTxs = @ \cup {txId}]
    /\ UNCHANGED <<ledger, branches, pendingRequests, responses, txStatus, nextSeq, statusNotifications>>

\* Next state relation
Next ==
    \/ \E c \in Clients, d \in 1..3 : SubmitTransaction(c, d)
    \/ \E req \in pendingRequests, b \in branches : ProcessTransaction(req, b)
    \/ \E txId \in DOMAIN txStatus : CommitTransaction(txId)
    \/ \E b \in branches, fp \in 0..MaxSeq : 
        /\ b \in DOMAIN ledger 
        /\ fp <= Len(ledger[b])
        /\ CreateBranch(b, fp)
    \/ \E c \in Clients, txId \in DOMAIN txStatus : ClientObservesTx(c, txId)

\* Fairness conditions
Fairness ==
    /\ \A req \in Request, b \in 0..MaxView : 
        WF_vars(req \in pendingRequests /\ b \in branches /\ ProcessTransaction(req, b))
    /\ \A txId \in TxID : WF_vars(txId \in DOMAIN txStatus /\ CommitTransaction(txId))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Alternative spec starting from mid-execution
SpecMidExecution == InitMidExecution /\ [][Next]_vars /\ Fairness

\* Safety Invariants

\* Type invariant
TypeInvariant ==
    /\ branches \subseteq 0..MaxView
    /\ \A b \in DOMAIN ledger : b \in 0..MaxView
    /\ \A txId \in DOMAIN txStatus : txStatus[txId] \in {"pending", "committed"}
    /\ \A c \in Clients : 
        /\ clientState[c].lastObserved \subseteq DOMAIN txStatus
        /\ clientState[c].pendingTxs \subseteq DOMAIN txStatus
        /\ clientState[c].committedTxs \subseteq DOMAIN txStatus

\* Read consistency: If a transaction observes tx1, and tx1 observed tx0, 
\* then the transaction must also observe tx0 (transitivity)
ReadConsistency ==
    \A b \in DOMAIN ledger :
        \A i \in 1..Len(ledger[b]) :
            LET tx == ledger[b][i]
            IN \A observedId \in tx.observedTxs :
                \A j \in 1..Len(ledger[b]) :
                    LET priorTx == ledger[b][j]
                    IN (priorTx.id = observedId /\ priorTx.id \in DOMAIN txStatus) =>
                       priorTx.observedTxs \subseteq tx.observedTxs

\* Branch consistency: Transactions on the same branch have consistent ordering
BranchConsistency ==
    \A b \in DOMAIN ledger :
        \A i, j \in 1..Len(ledger[b]) :
            (i < j) => TxIDLeq(ledger[b][i].id, ledger[b][j].id)

\* No duplicate transaction IDs within a branch
NoDuplicateTxIDs ==
    \A b \in DOMAIN ledger :
        \A i, j \in 1..Len(ledger[b]) :
            (i # j) => ledger[b][i].id # ledger[b][j].id

\* Committed transactions have valid IDs
CommittedTxValidity ==
    \A txId \in DOMAIN txStatus :
        txStatus[txId] = "committed" =>
        \E b \in DOMAIN ledger :
            \E i \in 1..Len(ledger[b]) :
                ledger[b][i].id = txId

\* Client state consistency: pending and committed sets are disjoint
ClientStateConsistency ==
    \A c \in Clients :
        clientState[c].pendingTxs \cap clientState[c].committedTxs = {}

\* Response validity: every response corresponds to a transaction in ledger
ResponseValidity ==
    \A resp \in responses :
        \E b \in DOMAIN ledger :
            \E i \in 1..Len(ledger[b]) :
                /\ ledger[b][i].id = resp.txId
                /\ resp.branch = b

\* All safety invariants combined
SafetyInvariant ==
    /\ TypeInvariant
    /\ ReadConsistency
    /\ BranchConsistency
    /\ NoDuplicateTxIDs
    /\ CommittedTxValidity
    /\ ClientStateConsistency
    /\ ResponseValidity

\* Liveness Properties

\* Every submitted transaction eventually gets processed
EventualProcessing ==
    \A req \in Request :
        (req \in pendingRequests) ~> (req \notin pendingRequests)

\* Every pending transaction eventually commits
EventualCommitment ==
    \A txId \in TxID :
        (txId \in DOMAIN txStatus /\ txStatus[txId] = "pending") ~>
        (txStatus[txId] = "committed")

\* Clients eventually observe all committed transactions
EventualObservation ==
    \A c \in Clients, txId \in TxID :
        (txId \in DOMAIN txStatus /\ txStatus[txId] = "committed") ~>
        (txId \in clientState[c].lastObserved)

=============================================================================