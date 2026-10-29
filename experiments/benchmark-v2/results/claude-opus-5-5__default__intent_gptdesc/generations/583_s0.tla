---------------------------- MODULE ReplicatedLedger ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,        \* finite set of client transaction identifiers
    MaxView     \* maximum view (leader epoch) explored

ASSUME /\ MaxView \in Nat \ {0}
       /\ IsFiniteSet(Txs)
       /\ Txs # {}

VARIABLES
    ledgerBranches, \* ledgerBranches[v] is the ledger branch of view v
    commitSeqNum,   \* single authoritative commit sequence number
    history,        \* history of client requests, responses and view changes
    committedLog    \* ghost: the committed prefix as of the last commit

vars == <<ledgerBranches, commitSeqNum, history, committedLog>>

-----------------------------------------------------------------------------
\* Helpers

Views   == 1..MaxView
MaxSeq  == Cardinality(Txs)
SeqNums == 1..MaxSeq
TxIDs   == Views \X SeqNums

Entry == [view : Views, tx : Txs]

CurrentView   == Len(ledgerBranches)
CurrentBranch == ledgerBranches[CurrentView]

Statuses == {"Committed", "Invalid"}

Events ==
         [type : {"RwTxRequest"}, tx : Txs]
    \cup [type : {"RwTxResponse"}, tx : Txs, tx_id : TxIDs]
    \cup [type : {"TxStatusReceived"}, tx_id : TxIDs, status : Statuses]
    \cup [type : {"ViewChange"}, view : Views,
          truncateTo : 0..MaxSeq, commitSeqNum : 0..MaxSeq]

Requested(tx) ==
    \E i \in 1..Len(history) :
        history[i].type = "RwTxRequest" /\ history[i].tx = tx

Responded(tx) ==
    \E i \in 1..Len(history) :
        history[i].type = "RwTxResponse" /\ history[i].tx = tx

ResponseWithId(tid) ==
    \E i \in 1..Len(history) :
        history[i].type = "RwTxResponse" /\ history[i].tx_id = tid

StatusReceived(tid) ==
    \E i \in 1..Len(history) :
        history[i].type = "TxStatusReceived" /\ history[i].tx_id = tid

InBranch(tx, branch) ==
    \E i \in 1..Len(branch) : branch[i].tx = tx

\* The transaction id <<v, s>> is durably committed
IsCommitted(tid) ==
    LET v == tid[1]
        s == tid[2]
    IN  /\ s <= commitSeqNum
        /\ CurrentBranch[s].view = v

\* The transaction id <<v, s>> can never become committed
CannotCommit(tid) ==
    LET v == tid[1]
        s == tid[2]
    IN  \/ /\ s <= commitSeqNum
           /\ CurrentBranch[s].view # v
        \/ /\ CurrentView > v
           /\ \/ s > Len(CurrentBranch)
              \/ CurrentBranch[s].view # v

IsPrefix(p, q) ==
    /\ Len(p) <= Len(q)
    /\ SubSeq(q, 1, Len(p)) = p

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ ledgerBranches = << << >> >>
    /\ commitSeqNum = 0
    /\ history = << >>
    /\ committedLog = << >>

-----------------------------------------------------------------------------
\* Actions

\* A client submits a read/write transaction
RwTxRequest(tx) ==
    /\ ~Requested(tx)
    /\ history' = Append(history, [type |-> "RwTxRequest", tx |-> tx])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum, committedLog>>

\* The leader of the current view executes the transaction and appends it
RwTxExecute(tx) ==
    /\ Requested(tx)
    /\ ~Responded(tx)
    /\ ~InBranch(tx, CurrentBranch)
    /\ ledgerBranches' =
         [ledgerBranches EXCEPT ![CurrentView] =
             Append(@, [view |-> CurrentView, tx |-> tx])]
    /\ UNCHANGED <<commitSeqNum, history, committedLog>>

\* The client receives the transaction id <<view, seqnum>> of its transaction
RwTxResponse(tx) ==
    /\ ~Responded(tx)
    /\ \E i \in 1..Len(CurrentBranch) :
         /\ CurrentBranch[i].tx = tx
         /\ history' = Append(history,
               [type  |-> "RwTxResponse",
                tx    |-> tx,
                tx_id |-> <<CurrentBranch[i].view, i>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum, committedLog>>

\* Commit sequence number advances (entries become durable)
AdvanceCommit(k) ==
    /\ commitSeqNum < k
    /\ k <= Len(CurrentBranch)
    /\ commitSeqNum' = k
    /\ committedLog' = SubSeq(CurrentBranch, 1, k)
    /\ UNCHANGED <<ledgerBranches, history>>

CommitStep == \E k \in SeqNums : AdvanceCommit(k)

\* View change: new view whose branch is a (possibly truncated) prefix of the
\* current branch; truncation never goes below the commit sequence number
ViewChange(k) ==
    /\ CurrentView < MaxView
    /\ k \in commitSeqNum..Len(CurrentBranch)
    /\ ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, k))
    /\ history' = Append(history,
          [type         |-> "ViewChange",
           view         |-> CurrentView + 1,
           truncateTo   |-> k,
           commitSeqNum |-> commitSeqNum])
    /\ UNCHANGED <<commitSeqNum, committedLog>>

\* Client is told its transaction is committed
StatusCommittedResponse(tid) ==
    /\ ResponseWithId(tid)
    /\ ~StatusReceived(tid)
    /\ IsCommitted(tid)
    /\ history' = Append(history,
          [type |-> "TxStatusReceived", tx_id |-> tid, status |-> "Committed"])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum, committedLog>>

\* Client is told its transaction is invalid (can never commit)
StatusInvalidResponse(tid) ==
    /\ ResponseWithId(tid)
    /\ ~StatusReceived(tid)
    /\ CannotCommit(tid)
    /\ history' = Append(history,
          [type |-> "TxStatusReceived", tx_id |-> tid, status |-> "Invalid"])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum, committedLog>>

Next ==
    \/ \E tx \in Txs : RwTxRequest(tx)
    \/ \E tx \in Txs : RwTxExecute(tx)
    \/ \E tx \in Txs : RwTxResponse(tx)
    \/ CommitStep
    \/ \E k \in 0..MaxSeq : ViewChange(k)
    \/ \E tid \in TxIDs : StatusCommittedResponse(tid)
    \/ \E tid \in TxIDs : StatusInvalidResponse(tid)

Spec == Init /\ [][Next]_vars /\ WF_vars(CommitStep)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ ledgerBranches \in Seq(Seq(Entry))
    /\ CurrentView \in Views
    /\ Len(CurrentBranch) <= MaxSeq
    /\ commitSeqNum \in 0..MaxSeq
    /\ commitSeqNum <= Len(CurrentBranch)
    /\ history \in Seq(Events)
    /\ committedLog \in Seq(Entry)

\* A Committed status is only given for the committed view and seqnum
CommittedStatusSafety ==
    \A i \in 1..Len(history) :
        (history[i].type = "TxStatusReceived" /\ history[i].status = "Committed")
            => /\ IsCommitted(history[i].tx_id)
               /\ ResponseWithId(history[i].tx_id)

\* Truncation never discards committed entries
TruncationSafety ==
    /\ \A i \in 1..Len(history) :
           history[i].type = "ViewChange"
               => history[i].truncateTo >= history[i].commitSeqNum
    /\ Len(committedLog) = commitSeqNum
    /\ IsPrefix(committedLog, CurrentBranch)

\* An Invalid status is justified: the tx id can never become committed
InvalidStatusSafety ==
    \A i \in 1..Len(history) :
        (history[i].type = "TxStatusReceived" /\ history[i].status = "Invalid")
            => /\ CannotCommit(history[i].tx_id)
               /\ ~IsCommitted(history[i].tx_id)

\* No transaction id receives both Committed and Invalid statuses
UniqueStatus ==
    \A i, j \in 1..Len(history) :
        (/\ history[i].type = "TxStatusReceived"
         /\ history[j].type = "TxStatusReceived"
         /\ history[i].tx_id = history[j].tx_id)
            => history[i].status = history[j].status

\* Once committed, the committed prefix is stable (temporal safety)
CommitMonotonic ==
    [][/\ commitSeqNum' >= commitSeqNum
       /\ IsPrefix(committedLog, committedLog')]_vars

\* Once invalid, never committed later (temporal)
InvalidStable ==
    \A tid \in TxIDs : [](CannotCommit(tid) => [](~IsCommitted(tid)))

-----------------------------------------------------------------------------
\* Liveness properties

\* Whenever there are uncommitted proposals in the current branch, the commit
\* sequence number eventually advances (unless the proposals are rolled back)
CommitProgress ==
    \A n \in 0..MaxSeq :
        (commitSeqNum = n /\ Len(CurrentBranch) > n)
            ~> (commitSeqNum > n \/ Len(CurrentBranch) <= n)

\* Eventually everything in the current branch is committed
EventuallyAllCommitted ==
    <>[](commitSeqNum = Len(CurrentBranch))

=============================================================================