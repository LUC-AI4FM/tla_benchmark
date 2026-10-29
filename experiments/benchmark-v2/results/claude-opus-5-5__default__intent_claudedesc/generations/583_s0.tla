---------------------------- MODULE MultiNodeLedger ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxRequest,        \* event: client submits a read-write transaction
    RwTxResponse,       \* event: service replies with the assigned TxID (view, seqnum)
    TxStatusReceived,   \* event: client learns final status of a transaction
    CommittedStatus,    \* status value: committed
    InvalidStatus,      \* status value: invalid (can never commit)
    HistoryLimit,       \* bound on the number of client-observable events
    ViewLimit           \* bound on the number of views (leader elections)

ASSUME HistoryLimit \in Nat /\ ViewLimit \in Nat \ {0}
ASSUME Cardinality({RwTxRequest, RwTxResponse, TxStatusReceived}) = 3
ASSUME CommittedStatus # InvalidStatus

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* ledgerBranches[v] is the ledger as seen in view v
    commitSeqNum     \* the current commit point (global)

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
\* Helpers

Last(s) == s[Len(s)]

CurrentView   == Len(ledgerBranches)
CurrentBranch == ledgerBranches[CurrentView]

Views == 1..ViewLimit
TxIds == 1..HistoryLimit
SeqNums == 1..HistoryLimit

LedgerEntry == [view : Views, tx : TxIds]

RequestEvent  == [type : {RwTxRequest}, tx : TxIds]
ResponseEvent == [type : {RwTxResponse}, tx : TxIds, view : Views, seqnum : SeqNums]
StatusEvent   == [type : {TxStatusReceived}, tx : TxIds, view : Views,
                  seqnum : SeqNums, status : {CommittedStatus, InvalidStatus}]

Min(a, b) == IF a <= b THEN a ELSE b

\* A transaction identified by (view, seqnum) is committed in the current state
IsCommitted(view, seqnum) ==
    /\ seqnum >= 1
    /\ seqnum <= commitSeqNum
    /\ CurrentBranch[seqnum].view = view

\* Conditions under which a transaction (view, seqnum) can never commit
CanNeverCommit(view, seqnum) ==
    \* Commit has passed seqnum but a different transaction was committed there
    \/ /\ seqnum <= commitSeqNum
       /\ CurrentBranch[seqnum].view # view
    \* Commit has not reached seqnum, but the view has advanced past the tx's view
    \* (new leaders only keep the committed prefix, so it was rolled back)
    \/ /\ seqnum > commitSeqNum
       /\ view < CurrentView
    \* Early invalidation: beyond the commit point and the current view's
    \* branch no longer holds this transaction at that position
    \/ /\ seqnum > commitSeqNum
       /\ \/ seqnum > Len(CurrentBranch)
          \/ CurrentBranch[seqnum].view # view

HasResponse(tx) ==
    \E j \in DOMAIN history :
        /\ history[j].type = RwTxResponse
        /\ history[j].tx = tx

HasStatus(tx) ==
    \E j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx = tx

InSomeBranch(tx) ==
    \E v \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[v] : ledgerBranches[v][k].tx = tx

-----------------------------------------------------------------------------
\* Initial state: one (empty) branch in view 1, nothing committed

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
\* Actions

\* A client submits a new read-write transaction (fresh id)
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The current leader executes a pending request, appending it to its ledger
RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~InSomeBranch(history[i].tx)
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
        /\ UNCHANGED <<history, commitSeqNum>>

\* The leader responds to the client with the assigned TxID (view, seqnum)
RwTxResponseAction ==
    \E i \in DOMAIN CurrentBranch :
        /\ Len(history) < HistoryLimit
        /\ ~HasResponse(CurrentBranch[i].tx)
        /\ history' = Append(history,
              [type   |-> RwTxResponse,
               tx     |-> CurrentBranch[i].tx,
               view   |-> CurrentBranch[i].view,
               seqnum |-> i])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Client is told its transaction is committed
StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ Len(history) < HistoryLimit
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx)
        /\ IsCommitted(history[i].view, history[i].seqnum)
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx     |-> history[i].tx,
               view   |-> history[i].view,
               seqnum |-> history[i].seqnum,
               status |-> CommittedStatus])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Client is told its transaction is invalid
StatusInvalidResponseAction ==
    \E i \in DOMAIN history :
        /\ Len(history) < HistoryLimit
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx)
        /\ CanNeverCommit(history[i].view, history[i].seqnum)
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx     |-> history[i].tx,
               view   |-> history[i].view,
               seqnum |-> history[i].seqnum,
               status |-> InvalidStatus])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Consensus advances the commit point within the current branch
AdvanceCommitSeqNumAction ==
    \E i \in (commitSeqNum + 1)..Len(CurrentBranch) :
        /\ commitSeqNum' = i
        /\ UNCHANGED <<history, ledgerBranches>>

\* Leader election: new view starts from the committed prefix only,
\* rolling back any uncommitted entries of the previous leader
ViewChangeAction ==
    /\ CurrentView < ViewLimit
    /\ ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, commitSeqNum))
    /\ UNCHANGED <<history, commitSeqNum>>

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ AdvanceCommitSeqNumAction
    \/ ViewChangeAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ history \in Seq(RequestEvent \cup ResponseEvent \cup StatusEvent)
    /\ Len(history) <= HistoryLimit
    /\ ledgerBranches \in Seq(Seq(LedgerEntry))
    /\ CurrentView \in Views
    /\ commitSeqNum \in Nat

\* The commit point always lies within the current branch
CommitWithinCurrentBranch ==
    commitSeqNum <= Len(CurrentBranch)

\* Entries in each branch never belong to a later view than the branch
BranchViewsWellFormed ==
    \A v \in DOMAIN ledgerBranches :
        \A k \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][k].view <= v

\* Consistency across branches: an entry from view w found in a later branch
\* is identical to the corresponding entry of every branch v with w <= v
\* (committed prefixes are copied unchanged across view changes)
LedgerBranchConsistency ==
    \A v1, v2 \in DOMAIN ledgerBranches :
        v1 < v2 =>
            \A k \in 1..Min(Len(ledgerBranches[v1]), Len(ledgerBranches[v2])) :
                ledgerBranches[v2][k].view <= v1 =>
                    ledgerBranches[v1][k] = ledgerBranches[v2][k]

\* Every branch created after the commit point was reached includes the
\* committed prefix of the current branch
CommittedPrefixConsistency ==
    \A v \in DOMAIN ledgerBranches :
        Len(ledgerBranches[v]) >= commitSeqNum =>
            \A k \in 1..commitSeqNum :
                CurrentBranch[k].view <= v =>
                    ledgerBranches[v][k] = CurrentBranch[k]

\* A transaction reported as committed is (and remains) committed
CommittedStatusValid ==
    \A i \in DOMAIN history :
        (history[i].type = TxStatusReceived /\ history[i].status = CommittedStatus)
            => IsCommitted(history[i].view, history[i].seqnum)

\* A transaction reported as invalid is not committed (in any reachable
\* state, hence it can never become committed: no resurrection)
InvalidStatusValid ==
    \A i \in DOMAIN history :
        (history[i].type = TxStatusReceived /\ history[i].status = InvalidStatus)
            => ~IsCommitted(history[i].view, history[i].seqnum)

\* No transaction receives contradictory statuses
UniqueStatus ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx = history[j].tx)
            => history[i].status = history[j].status

\* Each TxID (view, seqnum) is assigned to at most one transaction
UniqueTxIds ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].view = history[j].view
         /\ history[i].seqnum = history[j].seqnum)
            => history[i].tx = history[j].tx

Invariants ==
    /\ TypeOK
    /\ CommitWithinCurrentBranch
    /\ BranchViewsWellFormed
    /\ LedgerBranchConsistency
    /\ CommittedPrefixConsistency
    /\ CommittedStatusValid
    /\ InvalidStatusValid
    /\ UniqueStatus
    /\ UniqueTxIds

-----------------------------------------------------------------------------
\* Temporal (action) properties

\* Committed transactions are permanent: the commit point never moves back
\* and the committed prefix is never altered by any step (incl. view changes)
CommittedPrefixPermanent ==
    [][ /\ commitSeqNum' >= commitSeqNum
        /\ SubSeq(Last(ledgerBranches'), 1, commitSeqNum)
             = SubSeq(Last(ledgerBranches), 1, commitSeqNum) ]_vars

\* Once committed, a transaction stays committed
CommittedStaysCommitted ==
    [][ \A v \in Views : \A s \in SeqNums :
          IsCommitted(v, s) => IsCommitted(v, s)' ]_vars

\* Once a transaction can never commit, it stays that way (no resurrection)
InvalidStaysInvalid ==
    [][ \A i \in DOMAIN history :
          (/\ history[i].type = TxStatusReceived
           /\ history[i].status = InvalidStatus)
             => ~IsCommitted(history[i].view, history[i].seqnum)' ]_vars

THEOREM Spec => []Invariants
THEOREM Spec => CommittedPrefixPermanent /\ CommittedStaysCommitted /\ InvalidStaysInvalid
=============================================================================