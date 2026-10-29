---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RM

VARIABLES
    rmState,
    startTS,
    commitTS,
    nextTS,
    resolvedTS

vars == <<rmState, startTS, commitTS, nextTS, resolvedTS>>

States == {"idle", "prewrite", "committed", "aborted"}

MaxCheckTS == 105

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(a, b) == IF a >= b THEN a ELSE b

LockedStarts == { startTS[r] : r \in { s \in RM : rmState[s] = "prewrite" } }

CandidateRTS == Min(LockedStarts \cup {nextTS}) - 1

-----------------------------------------------------------------------------

RTTypeOK ==
    /\ rmState \in [RM -> States]
    /\ startTS \in [RM -> Nat]
    /\ commitTS \in [RM -> Nat]
    /\ nextTS \in Nat \ {0}
    /\ resolvedTS \in Nat

RTInit ==
    /\ rmState = [r \in RM |-> "idle"]
    /\ startTS = [r \in RM |-> 0]
    /\ commitTS = [r \in RM |-> 0]
    /\ nextTS = 1
    /\ resolvedTS = 0

Prewrite(r) ==
    /\ rmState[r] \in {"idle", "committed", "aborted"}
    /\ rmState' = [rmState EXCEPT ![r] = "prewrite"]
    /\ startTS' = [startTS EXCEPT ![r] = nextTS]
    /\ commitTS' = [commitTS EXCEPT ![r] = 0]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED resolvedTS

Commit(r) ==
    /\ rmState[r] = "prewrite"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ commitTS' = [commitTS EXCEPT ![r] = nextTS]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED <<startTS, resolvedTS>>

Abort(r) ==
    /\ rmState[r] = "prewrite"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<startTS, commitTS, nextTS, resolvedTS>>

Finish(r) == Commit(r) \/ Abort(r)

Resolve ==
    /\ CandidateRTS > resolvedTS
    /\ resolvedTS' = Max(resolvedTS, CandidateRTS)
    /\ UNCHANGED <<rmState, startTS, commitTS, nextTS>>

RTNext ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Abort(r)
    \/ Resolve

RTSpec ==
    /\ RTInit
    /\ [][RTNext]_vars
    /\ \A r \in RM : WF_vars(Finish(r))
    /\ WF_vars(Resolve)

-----------------------------------------------------------------------------

CommitConsistency ==
    \A r \in RM :
        rmState[r] = "committed" =>
            /\ commitTS[r] > startTS[r]
            /\ commitTS[r] < nextTS

ResolvedConsistency ==
    /\ resolvedTS < nextTS
    /\ \A r \in RM : rmState[r] = "prewrite" => startTS[r] > resolvedTS

ResolveLiveness ==
    \A t \in 0..MaxCheckTS : (nextTS > t) ~> (resolvedTS >= t)

StateConstraint == nextTS < 106

=============================================================================