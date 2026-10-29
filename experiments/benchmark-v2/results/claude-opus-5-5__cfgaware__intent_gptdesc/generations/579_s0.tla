```tla
ars, crashed>>

\* Failures: at most a minority of nodes crash at any time
Crash(n) ==
    /\ n \notin crashed
    /\ Majority(Nodes \ (crashed \cup {n}))
    /\ crashed' = crashed \cup {n}
    /\ UNCHANGED <<history, ledgerVars, nodeView, nodeLen>>

Recover(n) ==
    /\ n \in crashed
    /\ crashed' = crashed \ {n}
    /\ UNCHANGED <<history, ledgerVars, nodeView, nodeLen>>

-----------------------------------------------------------------------------
\* Next-state relation and specification

Next ==
    \/ ClientRwRequest
    \/ ClientRoRequest
    \/ Propose
    \/ RwRespond
    \/ RoRespond
    \/ StatusCommitted
    \/ StatusInvalid
    \/ Commit
    \/ \E m \in Nodes : Replicate(m)
    \/ \E n \in Nodes : ViewChange(n)
    \/ \E m \in Nodes : Truncate(m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Recover(n)

Fairness ==
    /\ WF_vars(Propose)
    /\ WF_vars(Commit)
    /\ \A m \in Nodes : WF_vars(Replicate(m))
    /\ \A m \in Nodes : WF_vars(Truncate(m))

MCSpecMultiNode == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Bound invariants

HistoryLimitInv == Len(history) <= HistoryLimit

ViewLimitInv == currentView - FirstBranch <= ViewLimit

TypeOK ==
    /\ currentView \in Nat
    /\ commitIndex \in 0..Len(CurLedger)
    /\ leader \in Nodes
    /\ crashed \subseteq Nodes
    /\ \A n \in Nodes : nodeView[n] \in DOMAIN ledgerBranches
    /\ \A n \in Nodes : nodeLen[n] \in 0..Len(ledgerBranches[nodeView[n]])

-----------------------------------------------------------------------------
\* Replica-level safety

\* Non-faulty nodes on the current view hold ledgers consistent with the
\* leader's ledger, hence agree on the committed prefix
CommittedPrefixConsistentInv ==
    \A m1, m2 \in Nodes \ crashed :
        (nodeView[m1] = currentView /\ nodeView[m2] = currentView) =>
            LET k == Min(Min(nodeLen[m1], nodeLen[m2]), commitIndex)
            IN SubSeq(NodeLedger(m1), 1, k) = SubSeq(NodeLedger(m2), 1, k)

\* Once committed, an entry stays in every later ledger state
CommitmentPreservedProp ==
    [][ /\ commitIndex' >= commitIndex
        /\ SubSeq(ledgerBranches'[currentView'], 1, commitIndex)
              = SubSeq(CurLedger, 1, commitIndex) ]_vars

\* Liveness: proposals in the current ledger are eventually committed
ProposalEventuallyCommitted ==
    \A t \in 1..HistoryLimit :
        (\E i \in DOMAIN CurLedger : CurLedger[i].tx = t)
            ~> (\/ \E i \in 1..commitIndex : CurLedger[i].tx = t
                \/ ~\E i \in DOMAIN CurLedger : CurLedger[i].tx = t)
```

```tla
-----------------------------------------------------------------------------
\* Client-observable invariants

AllReceivedIsFirstSentInv ==
    \A i \in RwResponseIdx \cup RoResponseIdx :
        \E j \in 1..(i - 1) :
            /\ history[j].type =
                  IF history[i].type = RwTxResponse THEN RwTxRequest ELSE RoTxRequest
            /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in CommittedRwResponseIdx :
        history[i].tx_id[2] < history[j].tx_id[2]
            => history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in RwResponseIdx \cup RoResponseIdx :
        \A t \in Range(history[i].observed) :
            \E j \in 1..(i - 1) :
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in RwResponseIdx :
        i # j => history[i].tx # history[j].tx

SameObservationsInv ==
    \A i, j \in RwResponseIdx :
        history[i].tx_id = history[j].tx_id
            => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in RwResponseIdx :
        i # j => history[i].tx_id # history[j].tx_id

UniqueTxRequestsInv ==
    \A i, j \in RwRequestIdx \cup RoRequestIdx :
        i # j => history[i].tx # history[j].tx

UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRwResponseIdx :
        i # j => history[i].tx_id[2] # history[j].tx_id[2]

CommittedOrInvalidStrongInv ==
    /\ \A i, j \in StatusIdx :
          history[i].tx_id = history[j].tx_id
              => history[i].status = history[j].status
    /\ \A a, b \in CommittedTxIds :
          a[2] = b[2] => a = b

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResponseIdx :
        history[i].tx_id[2] < history[j].tx_id[2]
            => IsPrefix(history[i].observed, history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwResponseIdx :
        \A j \in CommittedRwResponseIdx :
            history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in RwResponseIdx \cup RoResponseIdx :
        NoDup(history[i].observed)

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwResponseIdx :
        (\E k \in RwRequestIdx : k > i /\ history[k].tx = history[j].tx)
            => history[i].tx_id[2] < history[j].tx_id[2]

=============================================================================
```