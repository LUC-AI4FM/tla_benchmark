---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Clients,
    MaxViews,
    MaxSeqNums,
    MaxBranches

VARIABLES
    ledger,
    clientRequests,
    clientResponses,
    txnStatus,
    currentView,
    nextSeqNum,
    pendingTxns,
    committedTxns,
    observedBy

vars == <<ledger, clientRequests, clientResponses, txnStatus, currentView, 
          nextSeqNum, pendingTxns, committedTxns, observedBy>>

TxnId == [view: 1..MaxViews, seq: 1..MaxSeqNums]

NullTxnId == [view |-> 0, seq |-> 0]

Branch == 1..MaxBranches

TypeOK ==
    /\ ledger \in [Branch -> Seq(TxnId)]
    /\ clientRequests \in [Clients -> Seq([type: {"read_write"}, data: Nat])]
    /\ clientResponses \in [Clients -> Seq([txnId: TxnId \cup {NullTxnId}, 
                                            observed: SUBSET TxnId])]
    /\ txnStatus \in [TxnId -> {"unknown", "pending", "committed"}]
    /\ currentView \in 1..MaxViews
    /\ nextSeqNum \in [Branch -> 1..(MaxSeqNums + 1)]
    /\ pendingTxns \in SUBSET TxnId
    /\ committedTxns \in SUBSET TxnId
    /\ observedBy \in [TxnId -> SUBSET TxnId]

Init ==
    /\ ledger = [b \in Branch |-> <<>>]
    /\ clientRequests = [c \in Clients |-> <<>>]
    /\ clientResponses = [c \in Clients |-> <<>>]
    /\ txnStatus = [t \in TxnId |-> "unknown"]
    /\ currentView = 1
    /\ nextSeqNum = [b \in Branch |-> 1]
    /\ pendingTxns = {}
    /\ committedTxns = {}
    /\ observedBy = [t \in TxnId |-> {}]

InitAlt ==
    /\ ledger = [b \in Branch |-> 
        IF b = 1 THEN <<[view |-> 1, seq |-> 1], [view |-> 1, seq |-> 2]>>
        ELSE IF b = 2 THEN <<[view |-> 1, seq |-> 1], [view |-> 2, seq |-> 1]>>
        ELSE <<>>]
    /\ clientRequests = [c \in Clients |-> <<>>]
    /\ clientResponses = [c \in Clients |-> 
        IF c = CHOOSE x \in Clients : TRUE 
        THEN <<[txnId |-> [view |-> 1, seq |-> 1], observed |-> {}],
               [txnId |-> [view |-> 1, seq |-> 2], observed |-> {[view |-> 1, seq |-> 1]}]>>
        ELSE <<>>]
    /\ txnStatus = [t \in TxnId |-> 
        IF t = [view |-> 1, seq |-> 1] THEN "committed"
        ELSE IF t = [view |-> 1, seq |-> 2] THEN "committed"
        ELSE IF t = [view |-> 2, seq |-> 1] THEN "committed"
        ELSE "unknown"]
    /\ currentView = 2
    /\ nextSeqNum = [b \in Branch |-> 
        IF b = 1 THEN 3
        ELSE IF b = 2 THEN 2
        ELSE 1]
    /\ pendingTxns = {}
    /\ committedTxns = {[view |-> 1, seq |-> 1], [view |-> 1, seq |-> 2], [view |-> 2, seq |-> 1]}
    /\ observedBy = [t \in TxnId |-> 
        IF t = [view |-> 1, seq |-> 2] THEN {[view |-> 1, seq |-> 1]}
        ELSE IF t = [view |-> 2, seq |-> 1] THEN {[view |-> 1, seq |-> 1]}
        ELSE {}]

SubmitTransaction(c, branch) ==
    /\ Len(clientRequests[c]) < 3
    /\ nextSeqNum[branch] <= MaxSeqNums
    /\ currentView <= MaxViews
    /\ LET newTxnId == [view |-> currentView, seq |-> nextSeqNum[branch]]
           priorTxns == IF Len(ledger[branch]) > 0 
                        THEN {ledger[branch][i] : i \in 1..Len(ledger[branch])}
                        ELSE {}
           observedCommitted == priorTxns \cap committedTxns
       IN
       /\ txnStatus[newTxnId] = "unknown"
       /\ clientRequests' = [clientRequests EXCEPT ![c] = 
            Append(@, [type |-> "read_write", data |-> Len(@) + 1])]
       /\ clientResponses' = [clientResponses EXCEPT ![c] = 
            Append(@, [txnId |-> newTxnId, observed |-> observedCommitted])]
       /\ ledger' = [ledger EXCEPT ![branch] = Append(@, newTxnId)]
       /\ txnStatus' = [txnStatus EXCEPT ![newTxnId] = "pending"]
       /\ nextSeqNum' = [nextSeqNum EXCEPT ![branch] = @ + 1]
       /\ pendingTxns' = pendingTxns \cup {newTxnId}
       /\ observedBy' = [observedBy EXCEPT ![newTxnId] = observedCommitted]
       /\ UNCHANGED <<currentView, committedTxns>>

CommitTransaction(txnId) ==
    /\ txnId \in pendingTxns
    /\ txnStatus[txnId] = "pending"
    /\ txnStatus' = [txnStatus EXCEPT ![txnId] = "committed"]
    /\ pendingTxns' = pendingTxns \ {txnId}
    /\ committedTxns' = committedTxns \cup {txnId}
    /\ UNCHANGED <<ledger, clientRequests, clientResponses, currentView, 
                   nextSeqNum, observedBy>>

ViewChange ==
    /\ currentView < MaxViews
    /\ currentView' = currentView + 1
    /\ UNCHANGED <<ledger, clientRequests, clientResponses, txnStatus,
                   nextSeqNum, pendingTxns, committedTxns, observedBy>>

CreateBranch(sourceBranch, targetBranch) ==
    /\ sourceBranch \in Branch
    /\ targetBranch \in Branch
    /\ sourceBranch # targetBranch
    /\ Len(ledger[targetBranch]) = 0
    /\ Len(ledger[sourceBranch]) > 0
    /\ LET branchPoint == Len(ledger[sourceBranch]) \div 2 + 1
           prefix == SubSeq(ledger[sourceBranch], 1, branchPoint)
       IN
       /\ ledger' = [ledger EXCEPT ![targetBranch] = prefix]
       /\ nextSeqNum' = [nextSeqNum EXCEPT ![targetBranch] = branchPoint + 1]
    /\ UNCHANGED <<clientRequests, clientResponses, txnStatus, currentView,
                   pendingTxns, committedTxns, observedBy>>

Next ==
    \/ \E c \in Clients, b \in Branch : SubmitTransaction(c, b)
    \/ \E t \in TxnId : CommitTransaction(t)
    \/ ViewChange
    \/ \E s, t \in Branch : CreateBranch(s, t)

Spec == Init /\ [][Next]_vars

SpecAlt == InitAlt /\ [][Next]_vars

MCSpecMultiNodeReadsAlt == SpecAlt

ReadConsistency ==
    \A t1, t2 \in committedTxns :
        (t1 \in observedBy[t2]) => 
            (t1.view < t2.view \/ (t1.view = t2.view /\ t1.seq < t2.seq))

BranchConsistency ==
    \A b1, b2 \in Branch :
        \A i \in 1..Min(Len(ledger[b1]), Len(ledger[b2])) :
            (ledger[b1][i] = ledger[b2][i]) \/
            (\E j \in 1..(i-1) : ledger[b1][j] # ledger[b2][j])

Min(a, b) == IF a < b THEN a ELSE b

TransitiveObservation ==
    \A t1, t2, t3 \in committedTxns :
        ((t1 \in observedBy[t2]) /\ (t2 \in observedBy[t3])) =>
            (t1 \in observedBy[t3] \/ t1 = t3)

NoSelfObservation ==
    \A t \in TxnId : t \notin observedBy[t]

StatusMonotonicity ==
    \A t \in TxnId :
        (txnStatus[t] = "committed") => (t \in committedTxns)

Linearizability ==
    \A t1, t2 \in committedTxns :
        (t1 # t2) =>
            ((t1.view < t2.view) \/ 
             (t1.view = t2.view /\ t1.seq # t2.seq))

=============================================================================