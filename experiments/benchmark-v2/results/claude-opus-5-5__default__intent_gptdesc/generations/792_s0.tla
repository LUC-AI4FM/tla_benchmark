```tla
 is violated.
AssertSnapshot      == Assert(SnapshotConsistency, "Snapshot consistency violated")
AssertAtomic        == Assert(AtomicVisibility, "Atomic visibility violated")
AssertWriteConflict == Assert(WriteConflictFreedom, "Write-conflict prevention violated")
AssertSIOrder       == Assert(SIOrdering, "SI commit ordering violated")
AssertNonTx         == Assert(NonTxConsistency, "Nontransactional consistency violated")
AssertNoStuck       == Assert(NoStuckTransaction, "A pending transaction cannot proceed")

AssertAll ==
    /\ AssertSnapshot
    /\ AssertAtomic
    /\ AssertWriteConflict
    /\ AssertSIOrder
    /\ AssertNonTx
    /\ AssertNoStuck

-----------------------------------------------------------------------------
(* Action-level safety properties *)

\* A conflict abort happens only when a real write-write conflict exists.
NoSpuriousConflictAbort ==
    [][\A t \in TxId :
         (Active(t) /\ txStatus'[t] = "aborted"
                    /\ abortReason'[t] = "conflict") => Conflicted(t)]_vars

\* A commit never succeeds while a write-write conflict exists.
NoConflictingCommit ==
    [][\A t \in TxId :
         (Active(t) /\ txStatus'[t] = "committed") => ~Conflicted(t)]_vars

\* The committed history is append-only: commit order is never rewritten.
HistoryAppendOnly ==
    [][/\ Len(history') >= Len(history)
       /\ SubSeq(history', 1, Len(history)) = history]_vars

\* Finished transactions stay finished.
FinalityOfOutcome ==
    [][\A t \in TxId : Finished(t) => txStatus'[t] = txStatus[t]]_vars

-----------------------------------------------------------------------------
(* Liveness properties (hold under Fairness) *)

\* Under fair scheduling, every started transaction eventually finishes.
\* Hence no transaction is blocked forever (no deadlock).
EventuallyFinishes ==
    \A t \in TxId : Active(t) ~> Finished(t)

\* A transaction that never encounters a write conflict eventually
\* commits, unless its client voluntarily aborts it.
NonConflictingEventuallyCommit ==
    \A t \in TxId :
        []((Active(t) /\ [](~Conflicted(t))) =>
              <>(txStatus[t] = "committed" \/ abortReason[t] = "client"))

\* The system as a whole keeps making progress until all work is done.
\* No reachable state is stuck with pending transactions.
NoDeadlock ==
    []((\E c \in Client : clientTx[c] # NoTx) =>
          <>(\A c \in Client : clientTx[c] = NoTx))

-----------------------------------------------------------------------------
(* Symmetry reduction for model checking. *)
(* Transaction identifiers are fully interchangeable, and so are         *)
(* clients. Note: TLC's symmetry reduction is sound for checking         *)
(* invariants. It may miss violations of liveness properties, so check   *)
(* liveness without the SYMMETRY option.                                 *)

TxSymmetry     == Permutations(TxId)
ClientSymmetry == Permutations(Client)
Symmetry       == Permutations(TxId) \cup Permutations(Client)

-----------------------------------------------------------------------------
(* Theorems (proof obligations checked by TLC) *)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => NoSpuriousConflictAbort /\ NoConflictingCommit
THEOREM Spec => HistoryAppendOnly /\ FinalityOfOutcome
THEOREM Spec => EventuallyFinishes /\ NonConflictingEventuallyCommit /\ NoDeadlock

=============================================================================
```