---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS k1, k2

VARIABLES nextTS, rmState, rmStartTS, rmCommitTS, resolvedTS

vars == <<nextTS, rmState, rmStartTS, rmCommitTS, resolvedTS>>

RM == {k1, k2}

const_1571478437097222000 == {k1, k2}

constr_1571478437097223000 == nextTS < 106

-----------------------------------------------------------------------------

Max(a, b) == IF a >= b THEN a ELSE b

MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y

Locked == {r \in RM : rmState[r] = "prewrite"}

Candidate ==
    IF Locked = {}
    THEN nextTS - 1
    ELSE MinSet({rmStartTS[r] : r \in Locked}) - 1

RTTypeOK ==
    /\ nextTS \in Nat
    /\ rmState \in [RM -> {"init", "prewrite", "committed"}]
    /\ rmStartTS \in [RM -> Nat]
    /\ rmCommitTS \in [RM -> Nat]
    /\ resolvedTS \in Nat

RTInit ==
    /\ nextTS = 100
    /\ rmState = [r \in RM |-> "init"]
    /\ rmStartTS = [r \in RM |-> 0]
    /\ rmCommitTS = [r \in RM |-> 0]
    /\ resolvedTS = 99

Prewrite(r) ==
    /\ rmState[r] = "init"
    /\ rmState' = [rmState EXCEPT ![r] = "prewrite"]
    /\ rmStartTS' = [rmStartTS EXCEPT ![r] = nextTS]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED <<rmCommitTS, resolvedTS>>

Commit(r) ==
    /\ rmState[r] = "prewrite"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ rmCommitTS' = [rmCommitTS EXCEPT ![r] = nextTS]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED <<rmStartTS, resolvedTS>>

Resolve ==
    /\ Candidate > resolvedTS
    /\ resolvedTS' = Max(resolvedTS, Candidate)
    /\ UNCHANGED <<nextTS, rmState, rmStartTS, rmCommitTS>>

RTNext ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r)
    \/ Resolve

RTSpec ==
    /\ RTInit
    /\ [][RTNext]_vars
    /\ \A r \in RM : WF_vars(Commit(r))
    /\ WF_vars(Resolve)

-----------------------------------------------------------------------------

CommitConsistency ==
    \A r \in RM :
        /\ rmState[r] = "committed" => rmCommitTS[r] > rmStartTS[r]
        /\ rmState[r] # "init" => rmStartTS[r] < nextTS
        /\ rmState[r] = "committed" => rmCommitTS[r] < nextTS

ResolvedConsistency ==
    /\ resolvedTS < nextTS
    /\ \A r \in RM :
        rmState[r] = "prewrite" => rmStartTS[r] > resolvedTS

ResolveLiveness ==
    \A r \in RM :
        (rmState[r] = "committed") ~> (resolvedTS >= rmCommitTS[r])

=============================================================================